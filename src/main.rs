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

fn negate_bit<T>(x: T) -> LinearCombination
    where T: Into<LinearCombination>
{
    LinearCombination::from(Variable::One()) - x
}

fn scalar_to_bits_le<CS: ConstraintSystem>(
    cs: &mut CS,
    n_bits: usize,
    var: LinearCombination
) -> Result<Vec<Variable>, R1CSError> {
    // This is a helper function that caches the evaluation of the input variable so that it
    // doesn't get recomputed and verified for each bit allocation.
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
            let eq = negate_bit(lt.clone() + gt.clone());

            // Whether left bit i is < or > right bit i.
            // bit_lt = !l_bit && r_bit = (1 - l_bit) * r_bit
            // bit_gt = l_bit && !r_bit = l_bit * (1 - r_bit)
            let (_, _, bit_lt) = cs.multiply(negate_bit(l_bit), r_bit.into());
            let (_, _, bit_gt) = cs.multiply(l_bit.into(), negate_bit(r_bit));

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
    brackets: &TaxBrackets,
    values: &[Variable],
    expected: &Variable
) -> Result<(), R1CSError> {
    // Compute Σ values.
    let total = values.iter()
        .map(|val| (val.clone(), Scalar::one()))
        .collect::<LinearCombination>();

    let mut last_cutoff = Scalar::zero();
    let mut cumulative = LinearCombination::default();
    for (cutoff, rate) in brackets.0.iter() {
        let next_cutoff = Scalar::from(*cutoff);
        let rate_scalar = Scalar::from(*rate);

        let gt_last = lt_gate(cs, 64, last_cutoff.into(), total.clone())?;
        let gt_next = lt_gate(cs, 64, next_cutoff.into(), total.clone())?;

        let (_, _, between_last_next) = cs.multiply(gt_last.clone(), negate_bit(gt_next.clone()));

        let (_, _, between_value) = cs.multiply(
            total.clone() - last_cutoff,
            LinearCombination::from(between_last_next) * rate_scalar
        );
        let (_, _, exceeds_value) = cs.multiply(
            LinearCombination::from(next_cutoff - last_cutoff),
            gt_next * rate_scalar
        );
        cumulative = cumulative + between_value + exceeds_value;

        last_cutoff = next_cutoff;
    }

    cumulative = cumulative - expected.clone();

    cs.constrain(cumulative);
    Ok(())
}

fn compute_taxes(brackets: &TaxBrackets, total: u64) -> u64 {
    (0..brackets.0.len())
        .map(|i| {
            let last_cutoff = if i == 0 { 0u64 } else { brackets.0[i-1].0 };
            let (next_cutoff, rate) = brackets.0[i];
            let amount = if total > next_cutoff {
                next_cutoff - last_cutoff
            } else if total > last_cutoff {
                total - last_cutoff
            } else {
                0
            };
            amount * rate
        })
        .fold(0, |sum, v| sum + v)
}

fn main() {
    let brackets = TaxBrackets(vec![
        (952500, 10),
        (3870000, 12),
        (8250000, 22),
        (15750000, 24),
        (20000000, 32),
        (50000000, 35),
        (u64::MAX, 37),
    ]);

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(8192, 1);

    let mut prover_transcript = Transcript::new(b"zk taxes");

    let mut prover = Prover::new(
        &bp_gens,
        &pc_gens,
        &mut prover_transcript,
    );

    let mut rng = rand::thread_rng();

    let income_amounts = (0..4)
        // Multiply by 100 cents to ensure there is no rounding necessary.
        .map(|_| rng.gen_range(0, 100000) * 100)
        .collect::<Vec<_>>();
    let total_income = income_amounts.iter().fold(0, |sum, v| sum + v);
    let total_tax = compute_taxes(&brackets, total_income);

    println!("Total: {}, Taxes: {}", total_income, total_tax);

    let inputs = income_amounts.iter()
        .map(|value| (Scalar::from(*value), Scalar::random(&mut rng)))
        .collect::<Vec<_>>();
    let output_v = Scalar::from(total_tax);
    let output_r = Scalar::random(&mut rng);

    let (input_pts, input_vars) = inputs.iter()
        .map(|(v, r)| prover.commit(*v, *r))
        .unzip::<_, _, Vec<_>, Vec<_>>();
    let (output_pt, output_var) = prover.commit(output_v, output_r);

    synthesize(&mut prover, &brackets, &input_vars, &output_var).unwrap();
    let proof = prover.prove().unwrap();

    let mut verifier_transcript = Transcript::new(b"zk taxes");
    let mut verifier = Verifier::new(
        &bp_gens,
        &pc_gens,
        &mut verifier_transcript,
    );
    let input_vars = input_pts.iter()
        .map(|pt| verifier.commit(*pt))
        .collect::<Vec<_>>();
    let output_var = verifier.commit(output_pt);

    synthesize(&mut verifier, &brackets, &input_vars, &output_var).unwrap();
    assert!(verifier.verify(&proof).is_ok());

    println!("Success!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_bits_gadget() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let x = rng.gen::<u64>();

            let mut prover_transcript = Transcript::new(b"test");

            let mut prover = Prover::new(
                &bp_gens,
                &pc_gens,
                &mut prover_transcript,
            );

            let (in_pt, in_var) = prover.commit(x.into(), Scalar::random(&mut rng));
            let (out_pts, out_vars) = (0..64)
                .map(|i| {
                    prover.commit(((x >> i) & 1).into(), Scalar::random(&mut rng))
                })
                .unzip::<_, _, Vec<_>, Vec<_>>();

            let result = scalar_to_bits_le(&mut prover, 64, in_var.into()).unwrap();
            for (wire1, wire2) in result.into_iter().zip(out_vars.into_iter()) {
                prover.constrain(wire1 - wire2);
            }

            let proof = prover.prove().unwrap();

            let mut verifier_transcript = Transcript::new(b"test");
            let mut verifier = Verifier::new(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript,
            );

            let in_var = verifier.commit(in_pt);
            let out_vars = out_pts.into_iter()
                .map(|out_pt| verifier.commit(out_pt))
                .collect::<Vec<_>>();

            let result = scalar_to_bits_le(&mut verifier, 64, in_var.into()).unwrap();
            for (wire1, wire2) in result.into_iter().zip(out_vars.into_iter()) {
                verifier.constrain(wire1 - wire2);
            }

            assert!(verifier.verify(&proof).is_ok());
        }
    }

    #[test]
    fn test_lt_gadget() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(512, 1);

       let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let x1 = rng.gen::<u64>();
            let x2 = rng.gen::<u64>();
            let expected_out = if x1 < x2 { 1u64 } else { 0u64 };

            let mut prover_transcript = Transcript::new(b"test");

            let mut prover = Prover::new(
                &bp_gens,
                &pc_gens,
                &mut prover_transcript,
            );

            let (in1_pt, in1_var) = prover.commit(x1.into(), Scalar::random(&mut rng));
            let (in2_pt, in2_var) = prover.commit(x2.into(), Scalar::random(&mut rng));
            let (out_pt, out_var) = prover.commit(expected_out.into(), Scalar::random(&mut rng));
            let result = lt_gate(
                &mut prover,
                64,
                in1_var.into(),
                in2_var.into()
            ).unwrap();
            prover.constrain(result - out_var);

            let proof = prover.prove().unwrap();

            let mut verifier_transcript = Transcript::new(b"test");
            let mut verifier = Verifier::new(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript,
            );

            let in1_var = verifier.commit(in1_pt);
            let in2_var = verifier.commit(in2_pt);
            let out_var = verifier.commit(out_pt);
            let result = lt_gate(
                &mut verifier,
                64,
                in1_var.into(),
                in2_var.into()
            ).unwrap();
            verifier.constrain(result - out_var);

            assert!(verifier.verify(&proof).is_ok());
        }
    }
}
