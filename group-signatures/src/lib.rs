use blake2::VarBlake2b;
use blake2::digest::{Input, VariableOutput};
use ff::{Field, PrimeField, PrimeFieldRepr};
use group::{CurveAffine, CurveProjective};
use rand::{Rand, Rng};
use pairing::Engine;

struct GroupManagerKey<E: Engine> {
    x: E::Fr,
    y: E::Fr,
    t: E::Fr,  // Tracing secret key
    x_g1: E::G1,
    pub pubkey: GroupPublicKey<E>,
}

#[derive(Clone)]
struct GroupPublicKey<E: Engine> {
    g1: E::G1Affine,
    g2: E::G2Affine,
    x_g2: E::G2,
    y_g2: E::G2,
    t_g1: E::G1,  // Tracing public key
}

struct GroupSecretKey<E: Engine> {
    m: E::Fr,
    m_g1: E::G1,
    h_g1: E::G1,
    w_g1: E::G1,
    pubkey: GroupPublicKey<E>,
}

struct GroupSignature<E: Engine> {
    c: E::Fr,
    s_v: E::Fr,
    s_m: E::Fr,
}

fn gen<E: Engine, R: Rng>(rng: &mut R) -> GroupManagerKey<E> {
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

fn issue<E: Engine, R: Rng>(rng: &mut R, gm_key: &GroupManagerKey<E>, m_g1: &E::G1Affine)
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

fn sign<E: Engine, R: Rng>(rng: &mut R, key: &GroupSecretKey<E>, msg: &[u8]) -> GroupSignature<E> {
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

    // K = G_1^k
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

    // R_e = e(A, G_2^r_v * Y^r_m)
    let mut r_e_g2 = pubkey.y_g2.clone();
    r_e_g2.mul_assign(r_m);
    r_e_g2.add_assign(&pubkey.g2.mul(r_v));
    let r_e_gt = E::pairing(a_g1, r_e_g2);

    // R_k = G_1^r_k
    let r_k_g1 = pubkey.g1.mul(r_k);

    // R_l = M * T^k
    let mut r_l_g1 = pubkey.t_g1.clone();
    r_l_g1.mul_assign(r_k);
    r_l_g1.add_assign(&key.m_g1);

    // Sigma proof challenge
    let mut hash = VarBlake2b::new(32)
        .expect("32 bytes is a valid output size for Blake2b");
    hash.input(msg);
    // Wow, this is awful. Field should really have a serialization.
    hash.input(format!("{}", r_e_gt).as_bytes());
    hash.input(r_k_g1.into_affine().into_compressed());
    hash.input(r_l_g1.into_affine().into_compressed());

    let mut c = <E::Fr as PrimeField>::Repr::default();
    hash.variable_result(|output| {
        c.read_le(output).expect("reading from byte array cannot fail")
    });
    let c = E::Fr::from_repr(c).expect("hash output is the size of the field repr");

    // Sigma proof scalars

    // s_v = r_v + c * v
    let mut s_v = v;
    s_v.mul_assign(&c);
    s_v.add_assign(&r_v);

    // s_m = r_m + c * m
    let mut s_m = key.m.clone();
    s_m.mul_assign(&c);
    s_m.add_assign(&r_m);

    GroupSignature {
        c,
        s_v,
        s_m,
    }
}

//fn verify<E: Engine>(pubkey: &GroupPublicKey<E>, msg: &[u8], sig: &GroupSignature<E>) -> bool {
//
//}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;
    use pairing::bls12_381::{Fr, Bls12};

    #[test]
    fn test_gen() {
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
    }
}
