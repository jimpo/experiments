use bulletproofs::r1cs::{
    ConstraintSystem,
    LinearCombination,
    Prover,
    R1CSError,
    Variable,
    Verifier,
};
use bulletproofs::{
    BulletproofGens,
    PedersenGens,
};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::Rng;

fn synthesize<CS: ConstraintSystem>(cs: &mut CS, values: &[Variable], total: &Variable)
    -> Result<(), R1CSError> {
    // Enforce total - Σ values = 0.
    let diff = values.iter().fold(
        LinearCombination::from(total.clone()),
        |diff, val| diff - val.clone(),
    );
    cs.constrain(diff);
    Ok(())
}

fn main() {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(4, 1);

    let mut prover_transcript = Transcript::new(b"zk taxes");

    let mut prover = Prover::new(
        &bp_gens,
        &pc_gens,
        &mut prover_transcript,
    );

    let mut rng = rand::thread_rng();

    let values = (0..4)
        .map(|_| {
            let v = Scalar::from(rng.gen::<u64>());
            let r = Scalar::random(&mut rng);
            (v, r)
        })
        .collect::<Vec<_>>();
    let total_v = values.iter().fold(Scalar::zero(), |sum, v| sum + v.0);
    let total_r = Scalar::random(&mut rng);

    let (value_pts, value_vars) = values.iter()
        .map(|(v, r)| prover.commit(*v, *r))
        .unzip::<_, _, Vec<_>, Vec<_>>();
    let (total_pt, total_var) = prover.commit(total_v, total_r);

    synthesize(&mut prover, &value_vars, &total_var).unwrap();
    let proof = prover.prove().unwrap();

    let mut verifier_transcript = Transcript::new(b"zk taxes");
    let mut verifier = Verifier::new(
        &bp_gens,
        &pc_gens,
        &mut verifier_transcript,
    );
    let value_vars = value_pts.iter()
        .map(|pt| verifier.commit(*pt))
        .collect::<Vec<_>>();
    let total_var = verifier.commit(total_pt);

    synthesize(&mut verifier, &value_vars, &total_var).unwrap();
    assert!(verifier.verify(&proof).is_ok());

    println!("Success!");
}
