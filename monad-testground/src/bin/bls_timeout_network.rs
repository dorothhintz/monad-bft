use std::{
    collections::HashMap,
    net::{Ipv4Addr, SocketAddr, SocketAddrV4},
    ops::Deref,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};

use futures_util::StreamExt;
use monad_bls::{BlsSignature, BlsSignatureCollection};
use monad_chain_config::{
    revision::{ChainParams, MockChainRevision},
    MockChainConfig,
};
use monad_consensus::messages::{
    consensus_message::{ConsensusMessage, ProtocolMessage},
    message::TimeoutMessage,
};
use monad_consensus_state::ConsensusConfig;
use monad_consensus_types::{
    block::{MockExecutionProtocol, PassthruBlockPolicy},
    validator_data::{ValidatorData, ValidatorSetData},
};
use monad_crypto::certificate_signature::{
    CertificateKeyPair, CertificateSignature, CertificateSignaturePubKey,
};
use monad_dataplane::udp::DEFAULT_MTU;
use monad_execution_state_read::{InMemoryState, InMemoryStateInner};
use monad_executor::Executor;
use monad_executor_glue::{Command, MonadEvent, RouterCommand};
use monad_node_config::{FullNodeConfig, FullNodeRaptorCastConfig};
use monad_raptorcast::config::RaptorCastConfig;
use monad_secp::SecpSignature;
use monad_state::VerifiedMonadMessage;
use monad_types::{Epoch, NodeId, Round, RouterTarget, SeqNum, Stake};
use monad_updaters::ledger::MockableLedger;
use monad_validator::signature_collection::{
    SignatureCollection, SignatureCollectionKeyPairType,
};
use rand::{rngs::StdRng, Rng, SeedableRng};
use tokio::sync::{mpsc, watch};

#[path = "../executor.rs"]
mod executor;
use executor::{
    make_monad_executor, make_monad_state, ExecutorConfig, LedgerConfig, RouterConfig,
    StateConfig, ValSetConfig,
};

type OuterSig = SecpSignature;
type PubKey = CertificateSignaturePubKey<OuterSig>;
type SigCol = BlsSignatureCollection<PubKey>;
type Exec = MockExecutionProtocol;
type OutMsg = VerifiedMonadMessage<OuterSig, SigCol, Exec>;
type StateRead = InMemoryState<OuterSig, SigCol>;
type FullCommand = Command<
    MonadEvent<OuterSig, SigCol, Exec>,
    OutMsg,
    OuterSig,
    SigCol,
    Exec,
    PassthruBlockPolicy,
    StateRead,
    MockChainConfig,
    MockChainRevision,
>;

type OuterKey = <OuterSig as CertificateSignature>::KeyPairType;
type CertKey = SignatureCollectionKeyPairType<SigCol>;

const NUM_NODES: usize = 5;
const TARGET_ROUND: Round = Round(6);
const TARGET_QC_ROUND: Round = Round(5);
const PROPOSAL_SKEW: Duration = Duration::from_millis(150);
const OBSERVE_WINDOW: Duration = Duration::from_secs(3);

static CHAIN_PARAMS: ChainParams = ChainParams {
    tx_limit: 10_000,
    proposal_gas_limit: 300_000_000,
    proposal_byte_limit: 4_000_000,
    max_reserve_balance: 1_000_000_000_000_000_000,
    vote_pace: Duration::from_millis(0),
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Attack,
    Control,
}

impl Mode {
    fn parse() -> Self {
        match std::env::args().nth(1).as_deref() {
            Some("attack") => Self::Attack,
            Some("control") => Self::Control,
            other => panic!("usage: bls_timeout_network [attack|control], got {other:?}"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Role {
    M0,
    M1,
    T,
    U0,
    U1,
}

impl Role {
    fn stake(self) -> u64 {
        match self {
            Role::M0 => 5,
            Role::M1 => 20,
            Role::T | Role::U0 | Role::U1 => 25,
        }
    }

    fn honest(self) -> bool {
        matches!(self, Role::T | Role::U0 | Role::U1)
    }
}

#[derive(Clone)]
struct Material {
    outer_seed: [u8; 32],
    cert_seed: [u8; 32],
    node_id: NodeId<PubKey>,
    cert_pubkey: <CertKey as CertificateKeyPair>::PubKey,
    role: Role,
    index: usize,
}

impl Material {
    fn outer_key(&self) -> OuterKey {
        let mut seed = self.outer_seed;
        OuterKey::from_bytes(seed.as_mut_slice()).expect("valid secp seed")
    }

    fn cert_key(&self) -> CertKey {
        let mut seed = self.cert_seed;
        CertKey::from_bytes(seed.as_mut_slice()).expect("valid BLS seed")
    }
}

#[derive(Debug)]
enum AttackEvent {
    AdvanceRound(OutMsg),
    Proposal(OutMsg),
    TTimeout {
        version: u32,
        timeout: TimeoutMessage<OuterSig, SigCol, Exec>,
    },
}

#[derive(Debug)]
enum Instruction {
    Send { target: RouterTarget<PubKey>, message: OutMsg },
}

#[derive(Debug)]
struct NodeSummary {
    role: Role,
    round: Round,
    ledger_at_arm: Option<usize>,
    ledger_final: usize,
    created_qc: u64,
    created_tc: u64,
}

struct NodeConfig {
    role: Role,
    index: usize,
    executor: ExecutorConfig<OuterSig, SigCol, Exec>,
    state: StateConfig<OuterSig, SigCol>,
}

fn make_materials() -> Vec<Material> {
    let mut rng = StdRng::seed_from_u64(0xB15_CAFE_2026);
    let mut raw = (0..NUM_NODES)
        .map(|index| {
            let outer_seed = rng.gen::<[u8; 32]>();
            let cert_seed = rng.gen::<[u8; 32]>();
            let mut outer_copy = outer_seed;
            let outer = OuterKey::from_bytes(outer_copy.as_mut_slice()).unwrap();
            let mut cert_copy = cert_seed;
            let cert = CertKey::from_bytes(cert_copy.as_mut_slice()).unwrap();
            (
                index,
                outer_seed,
                cert_seed,
                NodeId::new(outer.pubkey()),
                cert.pubkey(),
            )
        })
        .collect::<Vec<_>>();

    let mut sorted = (0..NUM_NODES).collect::<Vec<_>>();
    sorted.sort_by_key(|idx| raw[*idx].3);
    let role_by_position = [Role::M0, Role::M1, Role::T, Role::U0, Role::U1];
    let mut roles = vec![Role::T; NUM_NODES];
    for (position, raw_index) in sorted.into_iter().enumerate() {
        roles[raw_index] = role_by_position[position];
    }

    raw.drain(..)
        .map(|(index, outer_seed, cert_seed, node_id, cert_pubkey)| Material {
            outer_seed,
            cert_seed,
            node_id,
            cert_pubkey,
            role: roles[index],
            index,
        })
        .collect()
}

fn build_configs(materials: &[Material]) -> Vec<NodeConfig> {
    let validators = ValidatorSetData(
        materials
            .iter()
            .map(|material| ValidatorData {
                node_id: material.node_id,
                stake: Stake::from(material.role.stake()),
                cert_pubkey: material.cert_pubkey,
            })
            .collect(),
    );

    let addresses = materials
        .iter()
        .map(|material| {
            let port = 45_100 + material.index as u16 * 100;
            SocketAddrV4::new(Ipv4Addr::LOCALHOST, port)
        })
        .collect::<Vec<_>>();
    let known_addresses = materials
        .iter()
        .zip(addresses.iter())
        .map(|(material, address)| (material.node_id, *address))
        .collect::<HashMap<_, _>>();

    materials
        .iter()
        .zip(addresses)
        .map(|(material, address)| NodeConfig {
            role: material.role,
            index: material.index,
            executor: ExecutorConfig {
                local_addr: SocketAddr::V4(address),
                known_addresses: known_addresses.clone(),
                router_config: RouterConfig::RaptorCast(RaptorCastConfig {
                    shared_key: Arc::new(material.outer_key()),
                    mtu: DEFAULT_MTU,
                    udp_message_max_age_ms: u64::MAX,
                    sig_verification_rate_limit: 10_000,
                    primary_instance: Default::default(),
                    secondary_instance: FullNodeRaptorCastConfig {
                        enable_publisher: false,
                        enable_client: false,
                        raptor10_fullnode_redundancy_factor: 2f32,
                        full_nodes_prioritized: FullNodeConfig { identities: vec![] },
                        round_span: Round(10),
                        invite_lookahead: Round(5),
                        max_invite_wait: Round(3),
                        deadline_round_dist: Round(3),
                        init_empty_round_span: Round(1),
                        max_group_size: 10,
                        max_num_group: 5,
                        invite_future_dist_min: Round(1),
                        invite_future_dist_max: Round(5),
                        invite_accept_heartbeat_ms: 100,
                    },
                    deterministic_protocol_rollout:
                        monad_raptorcast::v1_rollout::CURRENT_STAGE,
                }),
                ledger_config: LedgerConfig::Mock,
                val_set_config: ValSetConfig::Mock {
                    genesis_validator_data: validators.clone(),
                    epoch_length: SeqNum(2_000),
                },
                nodeid: material.node_id,
            },
            state: StateConfig {
                key: material.outer_key(),
                cert_key: material.cert_key(),
                epoch_length: SeqNum(2_000),
                epoch_start_delay: Round(50),
                validators: validators.clone(),
                consensus_config: ConsensusConfig {
                    execution_delay: SeqNum::MAX,
                    delta: Duration::from_millis(100),
                    statesync_to_live_threshold: SeqNum(600),
                    live_to_statesync_threshold: SeqNum(900),
                    start_execution_threshold: SeqNum(300),
                    chain_config: MockChainConfig::new(&CHAIN_PARAMS),
                    timestamp_latency_estimate_ns: 10_000_000,
                    _phantom: Default::default(),
                },
            },
        })
        .collect()
}

fn protocol(message: &OutMsg) -> Option<&ProtocolMessage<OuterSig, SigCol, Exec>> {
    match message {
        OutMsg::Consensus(verified) => Some(&verified.deref().deref().message),
        _ => None,
    }
}

fn filter_commands(
    role: Role,
    commands: Vec<FullCommand>,
    attack_tx: &mpsc::UnboundedSender<AttackEvent>,
) -> Vec<FullCommand> {
    let mut retained = Vec::with_capacity(commands.len());
    for command in commands {
        let Command::RouterCommand(RouterCommand::Publish { target, message }) = command else {
            retained.push(command);
            continue;
        };

        let mut drop_message = false;
        if let Some(protocol_message) = protocol(&message) {
            match (role, protocol_message) {
                (Role::M0, ProtocolMessage::AdvanceRound(advance))
                    if advance.last_round_certificate.round() == TARGET_QC_ROUND =>
                {
                    let _ = attack_tx.send(AttackEvent::AdvanceRound(message.clone()));
                    println!("HARNESS_CAPTURE role=M0 kind=advance_round qc_round={:?}", TARGET_QC_ROUND);
                    drop_message = true;
                }
                (Role::M1, ProtocolMessage::Proposal(proposal))
                    if proposal.proposal_round == TARGET_ROUND =>
                {
                    let _ = attack_tx.send(AttackEvent::Proposal(message.clone()));
                    println!("HARNESS_CAPTURE role=M1 kind=proposal round={:?}", TARGET_ROUND);
                    drop_message = true;
                }
                (Role::T, ProtocolMessage::Timeout(timeout))
                    if timeout.as_ref().tminfo.round == TARGET_ROUND
                        && timeout.as_ref().tminfo.high_tip_round == Round(0) =>
                {
                    let version = match &message {
                        OutMsg::Consensus(verified) => verified.deref().deref().version,
                        _ => unreachable!(),
                    };
                    let _ = attack_tx.send(AttackEvent::TTimeout {
                        version,
                        timeout: timeout.clone(),
                    });
                    println!("HARNESS_CAPTURE role=T kind=qc_timeout round={:?}", TARGET_ROUND);
                }
                (Role::M0 | Role::M1, ProtocolMessage::Timeout(timeout))
                    if timeout.as_ref().tminfo.round >= TARGET_ROUND =>
                {
                    drop_message = true;
                }
                (Role::M0 | Role::M1, ProtocolMessage::Vote(vote))
                    if vote.vote.round >= TARGET_ROUND =>
                {
                    drop_message = true;
                }
                (Role::M0 | Role::M1, ProtocolMessage::Proposal(proposal))
                    if proposal.proposal_round >= TARGET_ROUND =>
                {
                    drop_message = true;
                }
                _ => {}
            }
        }

        if !drop_message {
            retained.push(Command::RouterCommand(RouterCommand::Publish {
                target,
                message,
            }));
        }
    }
    retained
}

async fn run_node(
    config: NodeConfig,
    mut instruction_rx: mpsc::UnboundedReceiver<Instruction>,
    attack_tx: mpsc::UnboundedSender<AttackEvent>,
    mut stop_rx: watch::Receiver<bool>,
    armed: Arc<AtomicBool>,
) -> NodeSummary {
    let state_read = InMemoryStateInner::genesis(SeqNum(4));
    let (mut state, initial_commands) = make_monad_state(state_read.clone(), config.state);
    let mut executor = make_monad_executor(config.index, state_read, config.executor);
    executor.exec(initial_commands);

    let mut ledger_at_arm = None;
    loop {
        if armed.load(Ordering::SeqCst) && ledger_at_arm.is_none() {
            ledger_at_arm = Some(executor.ledger().get_finalized_blocks().len());
        }

        tokio::select! {
            changed = stop_rx.changed() => {
                if changed.is_err() || *stop_rx.borrow() {
                    break;
                }
            }
            Some(instruction) = instruction_rx.recv() => {
                match instruction {
                    Instruction::Send { target, message } => {
                        executor.exec(vec![Command::RouterCommand(RouterCommand::Publish { target, message })]);
                    }
                }
            }
            event = executor.next() => {
                let Some(event) = event else { break; };
                let commands = state.update(event);
                let commands = filter_commands(config.role, commands, &attack_tx);
                executor.exec(commands);
            }
        }
    }

    let round = state
        .consensus()
        .map(|consensus| consensus.get_current_round())
        .unwrap_or(Round(0));
    NodeSummary {
        role: config.role,
        round,
        ledger_at_arm,
        ledger_final: executor.ledger().get_finalized_blocks().len(),
        created_qc: state.metrics().consensus_events.created_qc.get(),
        created_tc: state.metrics().consensus_events.created_tc.get(),
    }
}

async fn coordinate(
    mode: Mode,
    materials: Vec<Material>,
    mut attack_rx: mpsc::UnboundedReceiver<AttackEvent>,
    instruction_txs: Vec<mpsc::UnboundedSender<Instruction>>,
    stop_tx: watch::Sender<bool>,
    armed: Arc<AtomicBool>,
) -> bool {
    let index_of = |role: Role| {
        materials
            .iter()
            .find(|material| material.role == role)
            .expect("role exists")
            .index
    };
    let m0_idx = index_of(Role::M0);
    let m1_idx = index_of(Role::M1);
    let t_idx = index_of(Role::T);
    let u0_idx = index_of(Role::U0);
    let u1_idx = index_of(Role::U1);

    let mut advance = None;
    let mut proposal = None;
    let mut schedule_sent = false;
    let mut armed_once = false;
    let deadline = Instant::now() + Duration::from_secs(15);

    while Instant::now() < deadline {
        let remaining = deadline.saturating_duration_since(Instant::now());
        let Some(event) = tokio::time::timeout(remaining, attack_rx.recv())
            .await
            .ok()
            .flatten()
        else {
            break;
        };

        match event {
            AttackEvent::AdvanceRound(message) => { advance.get_or_insert(message); }
            AttackEvent::Proposal(message) => { proposal.get_or_insert(message); }
            AttackEvent::TTimeout { version, mut timeout } if !armed_once => {
                let t_sig = timeout.as_ref().timeout_signature;
                if mode == Mode::Attack {
                    let mut compressed = t_sig.compress();
                    assert_eq!(compressed.len(), 96);
                    assert_eq!(compressed[0] & 0x80, 0x80);
                    assert_eq!(compressed[0] & 0x40, 0);
                    compressed[0] ^= 0x20;
                    timeout.0.timeout_signature = BlsSignature::uncompress(&compressed)
                        .expect("public G2 negation remains structurally valid");
                } else {
                    let tminfo = timeout.as_ref().tminfo.clone();
                    let high_extend = timeout.as_ref().high_extend.clone().into();
                    let last_round_certificate = timeout.as_ref().last_round_certificate.clone();
                    timeout = TimeoutMessage::new(
                        &materials[m0_idx].cert_key(),
                        tminfo,
                        high_extend,
                        true,
                        last_round_certificate,
                    );
                }

                let signed = ConsensusMessage {
                    version,
                    message: ProtocolMessage::Timeout(timeout),
                }
                .sign(&materials[m0_idx].outer_key());
                instruction_txs[m0_idx]
                    .send(Instruction::Send {
                        target: RouterTarget::Broadcast(Epoch(1)),
                        message: OutMsg::Consensus(signed),
                    })
                    .expect("M0 instruction channel open");
                armed.store(true, Ordering::SeqCst);
                armed_once = true;
                println!("HARNESS_ARMED mode={mode:?} round={TARGET_ROUND:?}");

                let stop_tx = stop_tx.clone();
                tokio::spawn(async move {
                    tokio::time::sleep(OBSERVE_WINDOW).await;
                    let _ = stop_tx.send(true);
                });
            }
            AttackEvent::TTimeout { .. } => {}
        }

        if !schedule_sent {
            if let (Some(advance), Some(proposal)) = (advance.take(), proposal.take()) {
                instruction_txs[m0_idx]
                    .send(Instruction::Send {
                        target: RouterTarget::PointToPoint(materials[t_idx].node_id),
                        message: advance,
                    })
                    .expect("send selective QC to T");
                println!("HARNESS_SEND kind=selective_qc to=T");
                tokio::time::sleep(PROPOSAL_SKEW).await;
                instruction_txs[m1_idx]
                    .send(Instruction::Send {
                        target: RouterTarget::PointToPoint(materials[u0_idx].node_id),
                        message: proposal.clone(),
                    })
                    .expect("send proposal to U0");
                instruction_txs[m1_idx]
                    .send(Instruction::Send {
                        target: RouterTarget::PointToPoint(materials[u1_idx].node_id),
                        message: proposal,
                    })
                    .expect("send proposal to U1");
                println!("HARNESS_SEND kind=selective_proposal to=U0,U1 skew_ms={}", PROPOSAL_SKEW.as_millis());
                schedule_sent = true;
            }
        }
    }

    if !armed_once {
        let _ = stop_tx.send(true);
    }
    armed_once
}

#[tokio::main]
async fn main() {
    let mode = Mode::parse();
    for index in 0..NUM_NODES {
        let _ = std::fs::remove_file(format!("./monad_controlpanel_{index}.sock"));
    }

    let materials = make_materials();
    println!("HARNESS_MODE {mode:?}");
    for material in &materials {
        println!(
            "HARNESS_ROLE index={} role={:?} node={:?} stake={} sorted_leader_r5={} sorted_leader_r6={}",
            material.index,
            material.role,
            material.node_id,
            material.role.stake(),
            material.role == Role::M0,
            material.role == Role::M1,
        );
    }

    let configs = build_configs(&materials);
    let (attack_tx, attack_rx) = mpsc::unbounded_channel();
    let (stop_tx, stop_rx) = watch::channel(false);
    let armed = Arc::new(AtomicBool::new(false));

    let mut instruction_txs = Vec::new();
    let mut handles = Vec::new();
    for config in configs {
        let (instruction_tx, instruction_rx) = mpsc::unbounded_channel();
        instruction_txs.push(instruction_tx);
        handles.push(tokio::spawn(run_node(
            config,
            instruction_rx,
            attack_tx.clone(),
            stop_rx.clone(),
            armed.clone(),
        )));
    }
    drop(attack_tx);

    let coordinator = tokio::spawn(coordinate(
        mode,
        materials.clone(),
        attack_rx,
        instruction_txs,
        stop_tx.clone(),
        armed,
    ));
    let armed_successfully = coordinator.await.expect("coordinator task");
    let summaries = futures_util::future::join_all(handles)
        .await
        .into_iter()
        .map(|result| result.expect("node task"))
        .collect::<Vec<_>>();

    println!("HARNESS_ARM_SUCCESS {armed_successfully}");
    for summary in &summaries {
        println!("HARNESS_SUMMARY {summary:?}");
    }

    assert!(armed_successfully, "attack sequence never armed");
    let honest = summaries
        .iter()
        .filter(|summary| summary.role.honest())
        .collect::<Vec<_>>();
    assert_eq!(honest.len(), 3);

    match mode {
        Mode::Attack => {
            assert!(
                honest.iter().all(|summary| summary.round == TARGET_ROUND),
                "all honest nodes must remain trapped in target round: {honest:?}"
            );
            assert!(
                honest.iter().all(|summary| summary.created_tc == 0),
                "attack run must not create a TC: {honest:?}"
            );
            println!("NETWORK_ATTACK_CONFIRMED");
        }
        Mode::Control => {
            assert!(
                honest.iter().all(|summary| summary.round > TARGET_ROUND),
                "valid-signature control must recover beyond target round: {honest:?}"
            );
            assert!(
                honest.iter().any(|summary| summary.created_tc > 0),
                "control must create a TC: {honest:?}"
            );
            println!("NETWORK_CONTROL_RECOVERED");
        }
    }
}
