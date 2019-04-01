use blake2::VarBlake2b;
use blake2::digest::{Input, VariableOutput};
use byteorder::{ByteOrder, LittleEndian};
use ff::{BitIterator, Field, PrimeField};
use group::{CurveAffine, CurveProjective};
use rand::{Rand, Rng};
use pairing::Engine;

pub struct GroupManagerKey<E: Engine> {
    x: E::Fr,
    y: E::Fr,
    t: E::Fr,  // Tracing secret key
    x_g1: E::G1,
    pub pubkey: GroupPublicKey<E>,
}

#[derive(Clone)]
pub struct GroupPublicKey<E: Engine> {
    g1: E::G1Affine,
    g2: E::G2Affine,
    x_g2: E::G2,
    y_g2: E::G2,
    t_g1: E::G1,  // Tracing public key
}

pub struct GroupSecretKey<E: Engine> {
    m: E::Fr,
    m_g1: E::G1,
    h_g1: E::G1,
    w_g1: E::G1,
    pubkey: GroupPublicKey<E>,
}

pub struct GroupSignature<E: Engine> {
    a_g1: E::G1,
    b_g1: E::G1,
    k_g1: E::G1,
    l_g1: E::G1,
    c: E::Fr,
    s_v: E::Fr,
    s_k: E::Fr,
    s_m: E::Fr,
}

pub fn gen<E: Engine, R: Rng>(rng: &mut R) -> GroupManagerKey<E> {
    let g1 = E::G1Affine::one();
    let g2 = E::G2Affine::one();
    let x = E::Fr::rand(rng);
    let y = E::Fr::rand(rng);
    let t = E::Fr::rand(rng);
    GroupManagerKey {
        x,
        y,
        t,
        x_g1: g1.mul(x.clone()),
        pubkey: GroupPublicKey {
            g1,
            g2,
            x_g2: g2.mul(x.clone()),
            y_g2: g2.mul(y),
            t_g1: g1.mul(t),
        }
    }
}

pub fn issue<E: Engine, R: Rng>(rng: &mut R, gm_key: &GroupManagerKey<E>, m_g1: &E::G1Affine)
    -> (E::G1, E::G1)
{
    let pubkey = &gm_key.pubkey;

    let h = E::Fr::rand(rng);
    let h_g1 = pubkey.g1.mul(h);

    let mut w_g1 = m_g1.mul(gm_key.y.clone());
    w_g1.add_assign(&gm_key.x_g1);
    w_g1.mul_assign(h);

    (h_g1, w_g1)
}

pub fn sign<E: Engine, R: Rng>(rng: &mut R, key: &GroupSecretKey<E>, msg: &[u8]) -> GroupSignature<E> {
    let pubkey = &key.pubkey;

    let u = E::Fr::rand(rng);
    let v = E::Fr::rand(rng);
    let k = E::Fr::rand(rng);

    // A = H^u
    let mut a_g1 = key.h_g1.clone();
    a_g1.mul_assign(u);

    // B = (W * H^v)^u
    let mut b_g1 = key.h_g1.clone();
    b_g1.mul_assign(v);
    b_g1.add_assign(&key.w_g1);
    b_g1.mul_assign(u);

    // K = G1^k
    let k_g1 = pubkey.g1.mul(k);

    // L = M * T^k
    let mut l_g1 = pubkey.t_g1.clone();
    l_g1.mul_assign(k);
    l_g1.add_assign(&key.m_g1);

    // Sigma proof nonces
    let r_v = E::Fr::rand(rng);
    let r_k = E::Fr::rand(rng);
    let r_m = E::Fr::rand(rng);

    // Sigma proof commitments

    // R_e = e(A, G2^r_v * Y^r_m)
    let mut r_e_g2 = pubkey.y_g2.clone();
    r_e_g2.mul_assign(r_m);
    r_e_g2.add_assign(&pubkey.g2.mul(r_v));
    let r_e_gt = E::pairing(a_g1, r_e_g2);

    // R_k = G1^r_k
    let r_k_g1 = pubkey.g1.mul(r_k);

    // R_l = G1^r_m * T^r_k
    let mut r_l_g1 = pubkey.t_g1.clone();
    r_l_g1.mul_assign(r_k);
    r_l_g1.add_assign(&pubkey.g1.mul(r_m));

    // Sigma proof challenge
    let mut hash = VarBlake2b::new(32)
        .expect("32 bytes is a valid output size for Blake2b");
    hash.input(msg);
    hash.input(a_g1.into_affine().into_compressed());
    hash.input(b_g1.into_affine().into_compressed());
    hash.input(k_g1.into_affine().into_compressed());
    hash.input(l_g1.into_affine().into_compressed());
    // Wow, this is awful. Field should really have a serialization.
    hash.input(format!("{}", r_e_gt).as_bytes());
    hash.input(r_k_g1.into_affine().into_compressed());
    hash.input(r_l_g1.into_affine().into_compressed());

    let c = hash_result_scalar::<E::Fr, _>(hash);

    // Sigma proof scalars

    // s_v = r_v + c * v
    let mut s_v = v;
    s_v.mul_assign(&c);
    s_v.add_assign(&r_v);

    // s_k = r_k + c * k
    let mut s_k = k;
    s_k.mul_assign(&c);
    s_k.add_assign(&r_k);

    // s_m = r_m + c * m
    let mut s_m = key.m.clone();
    s_m.mul_assign(&c);
    s_m.add_assign(&r_m);

    GroupSignature {
        a_g1,
        b_g1,
        k_g1,
        l_g1,
        c,
        s_v,
        s_k,
        s_m,
    }
}

pub fn verify<E: Engine>(pubkey: &GroupPublicKey<E>, msg: &[u8], sig: &GroupSignature<E>) -> bool {
    let mut neg_c = sig.c.clone();
    neg_c.negate();

    // R_e = e(A, G2^s_v * X^c * Y^s_k) / e(B, G2)^c
    let r_e_den = E::pairing(sig.b_g1.clone(), pubkey.g2.clone());
    let r_e_den = r_e_den.pow(neg_c.into_repr());

    let mut x_c = pubkey.x_g2.clone();
    x_c.mul_assign(sig.c.into_repr());

    let mut y_sm = pubkey.y_g2.clone();
    y_sm.mul_assign(sig.s_m.into_repr());

    let mut s_e_g2 = pubkey.g2.mul(sig.s_v.into_repr());
    s_e_g2.add_assign(&x_c);
    s_e_g2.add_assign(&y_sm);

    let mut r_e = E::pairing(sig.a_g1.clone(), s_e_g2);
    r_e.mul_assign(&r_e_den);

    // R_k = G1^s_k / K^c
    let mut r_k_den = sig.k_g1.clone();
    r_k_den.mul_assign(neg_c.into_repr());

    let mut r_k = pubkey.g1.mul(sig.s_k.into_repr());
    r_k.add_assign(&r_k_den);

    // R_l = G1^s_m * T^s_k / L^c
    let mut r_l_den = sig.l_g1.clone();
    r_l_den.mul_assign(neg_c.into_repr());

    let mut r_l = pubkey.t_g1.clone();
    r_l.mul_assign(sig.s_k.into_repr());
    r_l.add_assign(&pubkey.g1.mul(sig.s_m.into_repr()));
    r_l.add_assign(&r_l_den);

    // Sigma proof challenge
    let mut hash = VarBlake2b::new(32)
        .expect("32 bytes is a valid output size for Blake2b");
    hash.input(msg);
    hash.input(sig.a_g1.into_affine().into_compressed());
    hash.input(sig.b_g1.into_affine().into_compressed());
    hash.input(sig.k_g1.into_affine().into_compressed());
    hash.input(sig.l_g1.into_affine().into_compressed());
    // Wow, this is awful. Field should really have a serialization.
    hash.input(format!("{}", r_e).as_bytes());
    hash.input(r_k.into_affine().into_compressed());
    hash.input(r_l.into_affine().into_compressed());

    let c = hash_result_scalar::<E::Fr, _>(hash);

    // Return true if computed challenge equals proof challenge
    c == sig.c
}

pub fn trace<E: Engine>(gm_key: &GroupManagerKey<E>, sig: &GroupSignature<E>) -> E::G1 {
    // M = L * K^{-t}
    let mut neg_t = gm_key.t.clone();
    neg_t.negate();

    let mut m_g1 = sig.k_g1.clone();
    m_g1.mul_assign(neg_t.into_repr());
    m_g1.add_assign(&sig.l_g1);

    m_g1
}

fn hash_result_scalar<F: Field, H: VariableOutput>(hash: H) -> F {
    let one = F::one();

    let mut ret = F::zero();
    hash.variable_result(|output| {
        assert_eq!(output.len(), 32);
        let mut repr: [u64; 4] = [0; 4];
        LittleEndian::read_u64_into(output, &mut repr);

        for bit in BitIterator::new(repr) {
            ret.double();

            if bit {
                ret.add_assign(&one);
            }
        }
    });
    ret
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;
    use pairing::bls12_381::{Fr, Bls12};

    #[test]
    fn test_group_sig() {
        let mut rng = thread_rng();
        let gm_key = gen::<Bls12, _>(&mut rng);
        let pubkey = &gm_key.pubkey;

        let m = Fr::rand(&mut rng);
        let m_g1 = pubkey.g1.mul(m);
        let (h_g1, w_g1) = issue(&mut rng, &gm_key, &m_g1.into_affine());
        let key = GroupSecretKey {
            m,
            m_g1,
            h_g1,
            w_g1,
            pubkey: pubkey.clone()
        };

        let sig = sign(&mut rng, &key, b"Test");
        assert!(verify(&pubkey, b"Test", &sig));
        assert!(!verify(&pubkey, b"Fail", &sig));
        assert_eq!(trace(&gm_key, &sig), m_g1);
    }
}
