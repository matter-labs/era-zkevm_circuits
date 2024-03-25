use boojum::pairing::ff::*;

// base field, Q = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
#[derive(PrimeField)]
#[PrimeFieldModulus = "115792089210356248762697446949407573530086143415290314195533631308867097853951"]
#[PrimeFieldGenerator = "2"]
pub struct Fq(FqRepr);
