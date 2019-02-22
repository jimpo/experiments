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

use std::u64;

struct TaxBrackets(Vec<(u64, u64)>);

fn scalar_to_bits_le<CS: ConstraintSystem>(
    cs: &mut CS,
    n_bits: usize,
    var: LinearCombination
) -> Result<Vec<Variable>, R1CSError> {
    let mut cache_evaluation = {
        let get_bit = |scalar: &Scalar, i: usize| (scalar.as_bytes()[i >> 3] >> (i & 7)) & 1;
        let local_var = var.clone();
        let mut val_cache = None;
        move |eval: &dyn Fn(&LinearCombination) -> Scalar, i: usize| -> Result<u8, R1CSError> {
            if val_cache.is_none() {
                let val = eval(&local_var);
                let valid = (n_bits..256).any(|i| get_bit(&val, i) == 0);
                val_cache = Some(
                    if valid {
                        Ok(val)
                    } else {
                        Err(R1CSError::GadgetError {
                            description: format!("Value is not represented in {} bits", n_bits)
                        })
                    }
                );
            }
            val_cache.as_ref()
                .expect("the value must have been computed and cached by the block above")
                .as_ref()
                .map(|scalar| get_bit(scalar, i))
                .map_err(|e| e.clone())
        }
    };

    let bit_vars = (0..n_bits)
        .map(|i| {
            let (lhs, rhs, out) = cs.allocate(|eval| {
                let bit = cache_evaluation(eval, i)?;
                Ok((bit.into(), (1 - bit).into(), Scalar::zero()))
            })?;

            // Enforce that lhs variable represents a bit.
            // b (1 - b) = 0
            cs.constrain(LinearCombination::default() + rhs + lhs - Variable::One());
            cs.constrain(out.into());
            Ok(lhs)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let two_powers = (0..n_bits).map(|i| {
        let mut two_power_repr = [0u8; 32];
        two_power_repr[i >> 3] |= 1 << (i & 7);
        Scalar::from_bits(two_power_repr)
    });
    let bit_sum = bit_vars.iter()
        .cloned()
        .zip(two_powers)
        .collect::<LinearCombination>();

    // Enforce that var is equal to the inner product of the bits with powers of two.
    cs.constrain(var - bit_sum);

    Ok(bit_vars)
}

fn lt_gate<CS: ConstraintSystem>(
    cs: &mut CS,
    n_bits: usize,
    lhs: LinearCombination,
    rhs: LinearCombination
) -> Result<LinearCombination, R1CSError> {
    let lhs_bits = scalar_to_bits_le(cs, n_bits, lhs)?;
    let rhs_bits = scalar_to_bits_le(cs, n_bits, rhs)?;

    let zero = LinearCombination::default();

    // Iterate through bits from most significant to least, comparing each pair.
    let (lt, _) = lhs_bits.into_iter().zip(rhs_bits.into_iter())
        .rev()
        .fold((zero.clone(), zero.clone()), |(lt, gt), (l_bit, r_bit)| {
            // lt and gt are boolean LinearCombinations that are 1 if lhs < rhs or lhs > rhs
            // respectively after the first i most significant bits.
            // Invariant: lt & gt will never both be 1, so (lt || gt) = (lt + gt).

            // eq = !(lt || gt)
            let eq = LinearCombination::from(Variable::One()) - lt.clone() - gt.clone();

            // Whether left bit i is < or > right bit i.
            // bit_lt = !l_bit && r_bit = (1 - l_bit) * r_bit
            // bit_gt = l_bit && !r_bit = l_bit * (1 - r_bit)
            let (_, _, bit_lt) = cs.multiply(
                LinearCombination::from(Variable::One()) - l_bit, r_bit.into()
            );
            let (_, _, bit_gt) = cs.multiply(
                l_bit.into(), LinearCombination::from(Variable::One()) - r_bit
            );

            // new_lt = lt + eq && bit_lt
            //   -> lt_diff = new_lt - lt = eq * bit_lt
            // new_gt = gt + eq && bit_gt
            //   -> gt_diff = new_gt - gt = eq * bit_gt
            let (_, _, lt_diff) = cs.multiply(eq.clone(), bit_lt.into());
            let (_, _, gt_diff) = cs.multiply(eq.clone(), bit_gt.into());
            (lt + lt_diff, gt + gt_diff)
        });
    Ok(lt)
}

fn synthesize<CS: ConstraintSystem>(
    cs: &mut CS,
    _brackets: &TaxBrackets,
    values: &[Variable],
    total: &Variable
) -> Result<(), R1CSError> {
    // Enforce total - Σ values = 0.
    let diff = values.iter().fold(
        LinearCombination::from(total.clone()),
        |diff, val| diff - val.clone(),
    );
    cs.constrain(diff);
    Ok(())
}

fn main() {
    let brackets = TaxBrackets(vec![
        (9525, 10),
        (38700, 12),
        (82500, 22),
        (157500, 24),
        (200000, 32),
        (500000, 35),
        (u64::MAX, 37),
    ]);

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

    synthesize(&mut prover, &brackets, &value_vars, &total_var).unwrap();
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

    synthesize(&mut verifier, &brackets, &value_vars, &total_var).unwrap();
    assert!(verifier.verify(&proof).is_ok());

    println!("Success!");
}
