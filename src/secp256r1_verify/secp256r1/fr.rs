use boojum::pairing::ff::*;

// scalar field, R = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
#[derive(PrimeField)]
#[PrimeFieldModulus = "115792089210356248762697446949407573529996955224135760342422259061068512044369"]
#[PrimeFieldGenerator = "2"]
pub struct Fr(FrRepr);
