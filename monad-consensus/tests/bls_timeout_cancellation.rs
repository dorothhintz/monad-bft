use std::time::Duration;

use monad_bls::{BlsSignature, BlsSignatureCollection};
use monad_chain_config::{
    revision::{ChainParams, MockChainRevision},
    MockChainConfig,
};
use monad_consensus::{
    messages::message::TimeoutMessage,
    pacemaker::{Pacemaker, PacemakerCommand},
    validation::safety::Safety,
};
use monad_consensus_types::{
    block::{
        ConsensusBlockHeader, MockExecutionBody, MockExecutionProposedHeader,
        MockExecutionProtocol,
    },
    metrics::Metrics,
    payload::{ConsensusBlockBody, ConsensusBlockBodyInner, RoundSignature},
    quorum_certificate::QuorumCertificate,
    timeout::{HighExtend, TimeoutInfo},
    tip::ConsensusTip,
    voting::Vote,
    RoundCertificate,
};
use monad_crypto::{
    certificate_signature::{
        CertificateKeyPair, CertificateSignature, CertificateSignaturePubKey,
    },
    hasher::Hash,
    signing_domain,
};
use monad_secp::SecpSignature;
use monad_testutil::signing::{create_certificate_keys, create_keys};
use monad_types::{BlockId, Epoch, NodeId, Round, SeqNum, Stake};
use monad_validator::{
    epoch_manager::EpochManager,
    signature_collection::{SignatureCollection, SignatureCollectionKeyPairType},
    validator_mapping::ValidatorMapping,
    validator_set::{ValidatorSetFactory, ValidatorSetTypeFactory},
};

// This is intentionally an integration test: it exercises only public APIs.
// It does not alter production code or depend on private Pacemaker fields.

type OuterSignature = SecpSignature;
type BlsCollection = BlsSignatureCollection<CertificateSignaturePubKey<OuterSignature>>;
type Execution = MockExecutionProtocol;
type TestPacemaker = Pacemaker<
    OuterSignature,
    BlsCollection,
    Execution,
    MockChainConfig,
    MockChainRevision,
>;

static CHAIN_PARAMS: ChainParams = ChainParams {
    tx_limit: 10_000,
    proposal_gas_limit: 300_000_000,
    proposal_byte_limit: 4_000_000,
    max_reserve_balance: 1_000_000_000_000_000_000,
    vote_pace: Duration::from_millis(0),
};

fn make_qc<SCT: SignatureCollection>(
    epoch: Epoch,
    round: Round,
    outer_keys: &[SCT::NodeIdPubKey],
    certkeys: &[SignatureCollectionKeyPairType<SCT>],
    valmap: &ValidatorMapping<SCT::NodeIdPubKey, SignatureCollectionKeyPairType<SCT>>,
) -> QuorumCertificate<SCT> {
    let vote = Vote {
        id: BlockId(Hash([0u8; 32])),
        epoch,
        round,
    };
    let encoded = alloy_rlp::encode(vote);
    let sigs = outer_keys
        .iter()
        .zip(certkeys.iter())
        .map(|(key, certkey)| {
            let signature = <SCT::SignatureType as CertificateSignature>::sign::<
                signing_domain::Vote,
            >(encoded.as_ref(), certkey);
            (NodeId::new(*key), signature)
        });
    let sigcol = SCT::new::<signing_domain::Vote>(sigs, valmap, encoded.as_ref())
        .expect("valid QC signatures");
    QuorumCertificate::new(vote, sigcol)
}

fn make_qc_timeout(
    certkey: &SignatureCollectionKeyPairType<BlsCollection>,
    epoch: Epoch,
    round: Round,
    high_qc: QuorumCertificate<BlsCollection>,
) -> TimeoutMessage<OuterSignature, BlsCollection, Execution> {
    TimeoutMessage::new(
        certkey,
        TimeoutInfo {
            epoch,
            round,
            high_qc_round: high_qc.get_round(),
            high_tip_round: Round(0),
        },
        HighExtend::Qc(high_qc),
        true,
        None,
    )
}

fn make_tip_timeout(
    certkey: &SignatureCollectionKeyPairType<BlsCollection>,
    epoch: Epoch,
    round: Round,
    high_qc_round: Round,
    tip: ConsensusTip<OuterSignature, BlsCollection, Execution>,
) -> TimeoutMessage<OuterSignature, BlsCollection, Execution> {
    TimeoutMessage::new(
        certkey,
        TimeoutInfo {
            epoch,
            round,
            high_qc_round,
            high_tip_round: round,
        },
        HighExtend::Tip(tip),
        true,
        None,
    )
}

fn feed(
    pm: &mut TestPacemaker,
    metrics: &mut Metrics,
    epoch_manager: &EpochManager,
    valset: &impl monad_validator::validator_set::ValidatorSetType<
        NodeIdPubKey = CertificateSignaturePubKey<OuterSignature>,
    >,
    valmap: &ValidatorMapping<
        CertificateSignaturePubKey<OuterSignature>,
        SignatureCollectionKeyPairType<BlsCollection>,
    >,
    safety: &mut Safety<OuterSignature, BlsCollection, Execution>,
    author: NodeId<CertificateSignaturePubKey<OuterSignature>>,
    timeout: TimeoutMessage<OuterSignature, BlsCollection, Execution>,
) -> Vec<PacemakerCommand<OuterSignature, BlsCollection, Execution>> {
    pm.process_remote_timeout(
        metrics,
        epoch_manager,
        valset,
        valmap,
        safety,
        author,
        timeout,
    )
}

#[test]
fn cancelling_timeout_frames_honest_signer_and_prevents_tc() {
    // T=25%, U0=25%, U1=25%, M0=5%, M1=20% (silent).
    // Byzantine total is 25%, below one third.
    let outer_keys = create_keys::<OuterSignature>(5);
    let certkeys = create_certificate_keys::<BlsCollection>(5);
    let weights = [25u64, 25, 25, 5, 20];

    let validators = outer_keys
        .iter()
        .enumerate()
        .map(|(idx, key)| (NodeId::new(key.pubkey()), Stake::from(weights[idx])))
        .collect::<Vec<_>>();
    let valset = ValidatorSetFactory::default()
        .create(validators)
        .expect("valid weighted validator set");
    let valmap = ValidatorMapping::new(
        outer_keys
            .iter()
            .zip(certkeys.iter())
            .map(|(key, certkey)| (NodeId::new(key.pubkey()), certkey.pubkey()))
            .collect::<Vec<_>>(),
    );

    let epoch = Epoch(1);
    let round = Round(2);
    let epoch_manager = EpochManager::new(
        SeqNum(10_000),
        Round(10_000),
        &[(epoch, Round(0))],
    );
    let pubkeys = outer_keys
        .iter()
        .map(CertificateKeyPair::pubkey)
        .collect::<Vec<_>>();
    let high_qc = make_qc(
        epoch,
        round - Round(1),
        pubkeys.as_slice(),
        certkeys.as_slice(),
        &valmap,
    );
    let old_qc = make_qc(
        epoch,
        round - Round(2),
        pubkeys.as_slice(),
        certkeys.as_slice(),
        &valmap,
    );

    let t = make_qc_timeout(&certkeys[0], epoch, round, high_qc.clone());
    let timeout_digest = alloy_rlp::encode(&t.as_ref().tminfo);
    assert!(t
        .as_ref()
        .timeout_signature
        .verify::<signing_domain::Timeout>(timeout_digest.as_ref(), &certkeys[0].pubkey())
        .is_ok());

    let body = ConsensusBlockBody::<Execution>::new(ConsensusBlockBodyInner {
        execution_body: MockExecutionBody::default(),
    });
    let leader_idx = 4usize;
    let tip = ConsensusTip::new(
        &outer_keys[leader_idx],
        ConsensusBlockHeader {
            block_round: round,
            epoch,
            qc: high_qc.clone(),
            author: NodeId::new(outer_keys[leader_idx].pubkey()),
            seq_num: SeqNum(1),
            timestamp_ns: 1,
            round_signature: RoundSignature::new(round, &certkeys[leader_idx]),
            delayed_execution_results: vec![],
            execution_inputs: MockExecutionProposedHeader::default(),
            block_body_id: body.get_id(),
            base_fee: 0,
            base_fee_trend: 0,
            base_fee_moment: 0,
        },
        None,
    );
    let u0 = make_tip_timeout(
        &certkeys[1],
        epoch,
        round,
        round - Round(1),
        tip.clone(),
    );
    let expected_u1 = make_tip_timeout(
        &certkeys[2],
        epoch,
        round,
        round - Round(1),
        tip.clone(),
    );

    // Publicly negate T's compressed non-infinity G2 point. This is not a
    // signature under M0's registered BLS key, but it is structurally valid.
    let mut inverse = t.as_ref().timeout_signature.compress();
    assert_eq!(inverse.len(), 96);
    assert_eq!(inverse[0] & 0x80, 0x80);
    assert_eq!(inverse[0] & 0x40, 0);
    inverse[0] ^= 0x20;
    let cancelling = BlsSignature::uncompress(&inverse)
        .expect("negated compressed G2 point deserializes");
    assert!(cancelling.validate(true).is_ok());
    assert!(cancelling
        .verify::<signing_domain::Timeout>(timeout_digest.as_ref(), &certkeys[3].pubkey())
        .is_err());

    let mut malicious_m0 = make_qc_timeout(&certkeys[3], epoch, round, high_qc.clone());
    malicious_m0.0.timeout_signature = cancelling;
    let valid_m0 = make_qc_timeout(&certkeys[3], epoch, round, high_qc.clone());

    let mut pm = TestPacemaker::new(
        Duration::from_millis(100),
        MockChainConfig::new(&CHAIN_PARAMS),
        Duration::from_millis(100),
        &epoch_manager,
        RoundCertificate::Qc(high_qc.clone()),
    );
    let mut safety = Safety::new(RoundCertificate::Qc(old_qc.clone()), None);
    assert!(safety.is_safe_to_vote(round, None));
    safety.vote(round, None, tip.clone());

    let mut metrics = Metrics::default();
    let _ = feed(
        &mut pm,
        &mut metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut safety,
        NodeId::new(outer_keys[0].pubkey()),
        t.clone(),
    );
    let _ = feed(
        &mut pm,
        &mut metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut safety,
        NodeId::new(outer_keys[3].pubkey()),
        malicious_m0,
    );
    let commands = feed(
        &mut pm,
        &mut metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut safety,
        NodeId::new(outer_keys[1].pubkey()),
        u0.clone(),
    );

    // The f+1 transition generates U1's real local Tip timeout.
    let u1 = commands
        .into_iter()
        .find_map(|command| match command {
            PacemakerCommand::PrepareTimeout(info, high_extend, safe, last_rc) => Some(
                TimeoutMessage::new(&certkeys[2], info, high_extend, safe, last_rc),
            ),
            _ => None,
        })
        .expect("U1 produces local timeout after f+1 external stake");
    assert_eq!(u1, expected_u1);

    let _ = feed(
        &mut pm,
        &mut metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut safety,
        NodeId::new(outer_keys[2].pubkey()),
        u1,
    );
    assert_eq!(pm.get_current_round(), round);
    assert_eq!(metrics.consensus_events.created_tc.get(), 0);

    // A valid honest retransmission cannot make this receiver progress.
    let _ = feed(
        &mut pm,
        &mut metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut safety,
        NodeId::new(outer_keys[0].pubkey()),
        t.clone(),
    );
    assert_eq!(pm.get_current_round(), round);
    assert_eq!(metrics.consensus_events.created_tc.get(), 0);

    // Negative control: same stake, metadata and ordering, but M0 uses its
    // legitimate BLS signature. The TC forms and advances the round.
    let mut control = TestPacemaker::new(
        Duration::from_millis(100),
        MockChainConfig::new(&CHAIN_PARAMS),
        Duration::from_millis(100),
        &epoch_manager,
        RoundCertificate::Qc(high_qc.clone()),
    );
    let mut control_safety = Safety::new(RoundCertificate::Qc(old_qc), None);
    assert!(control_safety.is_safe_to_vote(round, None));
    control_safety.vote(round, None, tip);
    let mut control_metrics = Metrics::default();
    let _ = feed(
        &mut control,
        &mut control_metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut control_safety,
        NodeId::new(outer_keys[0].pubkey()),
        t,
    );
    let _ = feed(
        &mut control,
        &mut control_metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut control_safety,
        NodeId::new(outer_keys[3].pubkey()),
        valid_m0,
    );
    let control_commands = feed(
        &mut control,
        &mut control_metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut control_safety,
        NodeId::new(outer_keys[1].pubkey()),
        u0,
    );
    let control_u1 = control_commands
        .into_iter()
        .find_map(|command| match command {
            PacemakerCommand::PrepareTimeout(info, high_extend, safe, last_rc) => Some(
                TimeoutMessage::new(&certkeys[2], info, high_extend, safe, last_rc),
            ),
            _ => None,
        })
        .expect("control receiver produces local timeout");
    let _ = feed(
        &mut control,
        &mut control_metrics,
        &epoch_manager,
        &valset,
        &valmap,
        &mut control_safety,
        NodeId::new(outer_keys[2].pubkey()),
        control_u1,
    );
    assert_eq!(control.get_current_round(), round + Round(1));
    assert_eq!(control_metrics.consensus_events.created_tc.get(), 1);
}
