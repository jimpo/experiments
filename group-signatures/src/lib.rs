use pairing;
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
    k: E::Fr,
    h_g1: E::G1,
    w_g1: E::G1,
    pubkey: GroupPublicKey<E>,
}

struct GroupSignature<E: Engine> {
    r_u: E::G1,
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

fn issue<E: Engine, R: Rng>(rng: &mut R, gm_key: &GroupManagerKey<E>, k_g1: &E::G1Affine) -> (E::G1, E::G1) {
    let pubkey = &gm_key.pubkey;
    let h = E::Fr::rand(rng);
    let h_g1 = pubkey.g1.mul(h);

    let mut w_g1 = k_g1.mul(gm_key.y.clone());
    w_g1.add_assign(&gm_key.x_g1);
    w_g1.mul_assign(h);

    (h_g1, w_g1)
}

//fn sign<E: Engine>(key: &GroupSecretKey<E>, msg: &[u8]) -> GroupSignature<E> {
//
//}
//
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

        let k = Fr::rand(&mut rng);
        let k_g1 = pubkey.g1.mul(k);
        let (h_g1, w_g1) = issue(&mut rng, &gm_key, &k_g1.into_affine());
        let key = GroupSecretKey {
            k,
            h_g1,
            w_g1,
            pubkey: pubkey.clone()
        };
    }
}
