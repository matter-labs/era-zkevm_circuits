import json

# Defining the base prime field
q = Integer(21888242871839275222246405745257275088696311157297823662689037894645226208583) # EC group order
Fq = GF(q) 

# r is taken from https://hackmd.io/@jpw/bn254
k = Integer(12) # Embedding degree
t = Integer(4965661367192848881)
r = Integer(21888242871839275222246405745257275088548364400416034343698204186575808495617)
e = (q^(12)-1)/r

# Some magical constant exponent I have no idea about
m = 2*t*(6*t**2 + 3*t + 1)

# Making sure parameters are correctly defined
# See https://eprint.iacr.org/2010/354.pdf, Equation 1 for details.
assert q == 36*t**4 + 36*t**3 + 24*t**2 + 6*t + 1
assert r == 36*t**4 + 36*t**3 + 18*t**2 + 6*t + 1

# Defining the extensions
# Fq2...
K2.<x> = PolynomialRing(Fq)
Fq2.<u> = Fq.extension(x^2+1)

# Fq6...
K6.<y> = PolynomialRing(Fq2)
Fq6.<v> = Fq2.extension(y^3 - (u+9))

# Defining the Fq12 is a bit more tricky...
p = Fq.characteristic()
Fq12.<G> = GF(p^12)

i = sqrt(Fq12(-1))
R12.<Y> = PolynomialRing(Fq12)

j = (Y^3 - (i+9)).roots(multiplicities=False)[0]
w = sqrt(j)

P = w.minpoly()
Fq12.<W> = GF(p^12, modulus=P)

# Preparing helper debugging lambda functions
fq2_to_dictionary = lambda f : {
    'c0': str(f[0]), 
    'c1': str(f[1])
}
fq6_to_dictionary = lambda f : {
    'c0': {
        'c0': str(f[0][0]), 
        'c1': str(f[0][1])
    }, 
    'c1': {
        'c0': str(f[1][0]), 
        'c1': str(f[1][1])
    },
    'c2': {
        'c0': str(f[2][0]), 
        'c1': str(f[2][1])
    }
}
fq12_to_dictionary = lambda f: {
    'c0': { # Fq6
        'c0': { #Fq2
            'c0': str(f[0]+9*f[6]),
            'c1': str(f[6]),
        },
        'c1': { #Fq2
            'c0': str(f[2]+9*f[8]),
            'c1': str(f[8]),
        },
        'c2': { #Fq2
            'c0': str(f[4]+9*f[10]),
            'c1': str(f[10]),
        }
    }, 
    'c1': { # Fq6
        'c0': { #Fq2
            'c0': str(f[1]+9*f[7]),
            'c1': str(f[7]),
        },
        'c1': { #Fq2
            'c0': str(f[3]+9*f[9]),
            'c1': str(f[9]),
        },
        'c2': { #Fq2
            'c0': str(f[5]+9*f[11]),
            'c1': str(f[11]),
        }
    }
}

def c0c3c4_to_fq12(c0: Fq2, c3: Fq2, c4: Fq2) -> Fq12:
    return c0[0] + c0[1]*(W^6-9) + (c3[0]+c3[1]*(W^6-9))*W + (c4[0]+c4[1]*(W^6-9))*W^3

# Defining the G1 Curve and its generator
G1 = EllipticCurve(Fq, [0, 3])
G1_GEN = G1(1, 2)

# Defining the G2 Curve
b = 3 / (u + 9)
G2 = EllipticCurve(Fq2, [0, b])
G2_GEN = G2(10857046999023057135944570762232829481370756359578518086990519993285655852781+
            11559732032986387107991004021392285783925812861821192530917403151452391805634*u,
            8495653923123431417604973247489272438418190587263600148770280649306958101930+
            4082367875863433681332203403145435568316851327593401208105741076214120093531*u)

# Converts a tuple (X : Y : Z) from Fq2^3 to a point in G2 
# using Jacobian coordinates
def tuple_to_g2(t: tuple[Fq2, Fq2, Fq2]) -> G2:
    return G2(t[0]/t[2]^2, t[1]/t[2]^3)

# Helper debugging functions
g1_point_to_dictionary = lambda point : {
    'x': str(point[0]),
    'y': str(point[1])
}
g2_point_to_dictionary = lambda point : {
    'x': {
        'c0': str(point[0][0]), 
        'c1': str(point[0][1])
    }, 
    'y': {
        'c0': str(point[1][0]), 
        'c1': str(point[1][1])
    }
}

# Some coefficients for easier life
SIX_U_PLUS_TWO_WNAF = [
    0, 0, 0, 1, 0, 1, 0, -1, 
    0, 0, 1, -1, 0, 0, 1, 0, 
    0, 1, 1, 0, -1, 0, 0, 1, 
    0, -1, 0, 0, 0, 0, 1, 1, 
    1, 0, 0, -1, 0, 0, 1, 0, 
    0, 0, 0, 0, -1, 0, 0, 1, 
    1, 0, 0, -1, 0, 0, 0, 1, 
    1, 0, -1, 0, 0, 1, 0, 1, 1
]

# Converts the Montgomery form represented by 4 64-bit limbs to an integer in Fq
def from_limbs(limbs):
    montomery = limbs[0] | (limbs[1] << 64) | (limbs[2] << 128) | (limbs[3] << 192)
    return Fq(montomery) * Fq(2^(-256))

# Converts the Fq number to 4 64-bit limbs in Montgomery form
def to_montgomery_limbs(number: Fq):
    number = number * Fq(2^(256))
    number = Integer(number)

    # Building limbs
    limb_1 = number % 2**64
    limb_2 = (number // 2**64) % 2**64
    limb_3 = (number // 2**128) % 2**64
    limb_4 = (number // 2**192) % 2**64

    return [limb_1, limb_2, limb_3, limb_4]

# This is for the last step of Miller loop
FROBENIUS_COEFF_FQ6_C1_1 = from_limbs([
    0xb5773b104563ab30,
    0x347f91c8a9aa6454,
    0x7a007127242e0991,
    0x1956bcd8118214ec,
]) + from_limbs([
    0x6e849f1ea0aa4757, 
    0xaa1c7b6d89f89141, 
    0xb6e713cdfae0ca3a, 
    0x26694fbb4e82ebc3,
])*u
assert FROBENIUS_COEFF_FQ6_C1_1 == (9+u)**((q-1)/3), 'FROBENIUS_COEFF_FQ6_C1_1 is not correct!'

# Verifying that to_montgomery_limbs function is indeed correct
assert to_montgomery_limbs(from_limbs([
    0xb5773b104563ab30,
    0x347f91c8a9aa6454,
    0x7a007127242e0991,
    0x1956bcd8118214ec,
])) == [
    0xb5773b104563ab30,
    0x347f91c8a9aa6454,
    0x7a007127242e0991,
    0x1956bcd8118214ec,
], "to_montgomery_limbs function is incorrect"

# (9+u)**((q-1)/2)
XI_TO_Q_MINUS_1_OVER_2 = from_limbs([
    0xe4bbdd0c2936b629, 
    0xbb30f162e133bacb, 
    0x31a9d1b6f9645366, 
    0x253570bea500f8dd,
]) + from_limbs([
    0xa1d77ce45ffe77c7, 
    0x07affd117826d1db, 
    0x6d16bd27bb7edc6b, 
    0x2c87200285defecc,
])*u
assert XI_TO_Q_MINUS_1_OVER_2 == (9+u)**((q-1)/2), 'Non-XI_TO_Q_MINUS_1_OVER_2 is not correct!'

# (9+u)**((q^2-1)/3)
FROBENIUS_COEFF_FQ6_C1_2 = from_limbs([
    0x3350c88e13e80b9c,
    0x7dce557cdb5e56b9,
    0x6001b4b8b615564a,
    0x2682e617020217e0,
]) + from_limbs([
    0x0, 
    0x0, 
    0x0, 
    0x0,
])*u
assert FROBENIUS_COEFF_FQ6_C1_2 == (9+u)**((q^2-1)/3), 'FROBENIUS_COEFF_FQ6_C1_2 is not correct!'

# --- Line functions tested ---
# Original implementation from https://eprint.iacr.org/2010/354.pdf

def doubling_step(Q: G2, P: G2):
    X_Q, Y_Q, Z_Q = copy(Q[0]), copy(Q[1]), copy(Q[2])
    x_P, y_P = copy(P[0]), copy(P[1])

    tmp0 = X_Q**2
    tmp1 = Y_Q**2
    tmp2 = tmp1^2
    tmp3 = (tmp1 + X_Q)^2 - tmp0 - tmp2
    tmp3 = 2*tmp3
    tmp4 = 3*tmp0
    tmp6 = X_Q + tmp4
    tmp5 = tmp4^2
    X_T = tmp5 - 2*tmp3
    Z_T = (Y_Q + Z_Q)^2 - tmp1 - Z_Q^2
    Y_T = (tmp3 - X_T) * tmp4 - 8*tmp2
    tmp3 = -2*tmp4*Z_Q^2
    tmp3 = tmp3*x_P
    tmp6 = tmp6^2 - tmp0 - tmp5 - 4*tmp1
    tmp0 = 2*Z_T*Z_Q^2
    tmp0 = tmp0 * y_P

    return (tmp0, tmp3, tmp6), (X_T, Y_T, Z_T)

def addition_step(Q: G2, R: G2, P: G1):
    X_Q, Y_Q, Z_Q = copy(Q[0]), copy(Q[1]), copy(Q[2])
    X_R, Y_R, Z_R = copy(R[0]), copy(R[1]), copy(R[2])
    x_P, y_P = copy(P[0]), copy(P[1])

    t0 = X_Q * Z_R^2
    t1 = (Y_Q + Z_R)^2 - Y_Q^2 - Z_R^2
    t1 = t1 * Z_R^2
    t2 = t0 - X_R
    t3 = t2^2 
    t4 = 4*t3
    t5 = t4 * t2
    t6 = t1 - 2*Y_R
    t9 = t6 * X_Q
    t7 = X_R*t4
    X_T = t6^2 - t5 - 2*t7
    Z_T = (Z_R + t2)^2 - Z_R^2 - t3
    t10 = Y_Q + Z_T
    t8 = (t7 - X_T)*t6
    t0 = 2*Y_R*t5
    Y_T = t8 - t0
    t10 = t10^2 - Y_Q^2 - Z_T^2
    t9 = 2*t9 - t10
    t10 = 2*Z_T*y_P
    t6 = -t6
    t1 = 2*t6*x_P

    return (t10, t1, t9), (X_T, Y_T, Z_T)

LINE_FUNCTIONS_TESTS_NUMBER = 1

print('Preparing the line functions tests...')
tests_dict = {'tests': []}

for _ in range(LINE_FUNCTIONS_TESTS_NUMBER):
    # Generating two random points
    R = G2.random_point()
    Q = G2.random_point()
    P = G1.random_point()
    
    # Testing the line functions
    (c0_1, c3_1, c4_1), T1 = doubling_step(R, P)
    (c0_2, c3_2, c4_2), T2 = doubling_step(Q, P)
    (c0_3, c3_3, c4_3), T3 = addition_step(R, Q, P)
    (c0_4, c3_4, c4_4), T4 = addition_step(Q, T1, P)

    # Checking point correctness
    assert tuple_to_g2(T1) == 2*R, 'Doubling step 1 point is wrong!'
    assert tuple_to_g2(T2) == 2*Q, 'Doubling step 2 point is wrong!'
    assert tuple_to_g2(T3) == R+Q, 'Addition step point is wrong!'
    assert tuple_to_g2(T4) == 2*R+Q, 'Doubling and addition step point is wrong!'

    # Adding the test to the dictionary
    tests_dict['tests'].append({
        'g2_point_1': g2_point_to_dictionary(R),
        'g2_point_2': g2_point_to_dictionary(Q),
        'g1_point': g1_point_to_dictionary(P),
        'expected': {
            'doubling_1': {
                'point': g2_point_to_dictionary(2*R),
                'c0': fq2_to_dictionary(c0_1),
                'c3': fq2_to_dictionary(c3_1),
                'c4': fq2_to_dictionary(c4_1)
            },
            'doubling_2': {
                'point': g2_point_to_dictionary(2*Q),
                'c0': fq2_to_dictionary(c0_2),
                'c3': fq2_to_dictionary(c3_2),
                'c4': fq2_to_dictionary(c4_2)
            },
            'addition': {
                'point': g2_point_to_dictionary(R+Q),
                'c0': fq2_to_dictionary(c0_3),
                'c3': fq2_to_dictionary(c3_3),
                'c4': fq2_to_dictionary(c4_3)
            },
            'doubling_1_and_addition': {
                'point': g2_point_to_dictionary(2*R+Q),
                'c0': fq2_to_dictionary(c0_4),
                'c3': fq2_to_dictionary(c3_4),
                'c4': fq2_to_dictionary(c4_4)
            }
        }
    })

print('Line and tangent functions evaluations completed!')

# Saving the json file
FILE_NAME = '../json/ec_pairing/line_functions_tests.json'

print(f'Saving the line function tests to {FILE_NAME}...')

with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

# --- Final exponentiation tests ---

# Calculates the easy part of the exponentiation, that is
# `r^((p^(k) - 1) / Phi_k(p))` where
# `Phi_{12}(p) = p^4 - p^2 + 1` is a 12th cyclotomic polynomial.
def easy_part(f: Fq12) -> Fq12:
    return f**((q**k - 1) // (q**4-q**2+1))

# Reference implementation of the classical final exponentiation
def final_exp(r: Fq12) -> Fq12:
    r = easy_part(r)
    x = copy(t)
    fp = copy(r)
    fp = fp**(q)
    fp2 = copy(r)
    fp2 = fp2**(q**2)
    fp3 = copy(fp2)
    fp3 = fp3**(q)
    fu = copy(r)
    fu = fu**x
    fu2 = copy(fu)
    fu2 = fu2**x
    fu3 = copy(fu2)
    fu3 = fu3**x
    y3 = copy(fu)
    y3 = y3**q
    fu2p = copy(fu2)
    fu2p = fu2p**q
    fu3p = copy(fu3)
    fu3p = fu3p**q
    y2 = copy(fu2)
    y2 = y2**(q**2)
    y0 = copy(fp)
    y0 = y0 * fp2
    y0 = y0 * fp3
    y1 = copy(r)
    y1 = y1.conjugate()
    y5 = copy(fu2)
    y5 = y5.conjugate()
    y3 = y3.conjugate()
    y4 = copy(fu)
    y4 = y4 * fu2p
    y4 = y4.conjugate()
    y6 = copy(fu3)
    y6 = y6*fu3p
    y6 = y6.conjugate()
    y6 = y6**2
    y6 = y6 * y4
    y6 = y6 * y5
    t1 = copy(y3)
    t1 = t1 * y5
    t1 = t1 * y6
    y6 = y6 * y2
    t1 = t1**2
    t1 = t1 * y6
    t1 = t1**2 
    t0 = copy(t1)
    t0 = t0 * y1
    t1 = t1 * y0
    t0 = t0**2
    t0 = t0 * t1
    return t0

def final_exp_devegili(f: Fq12) -> Fq12:
    f = easy_part(f)
    t = Integer(4965661367192848881)
    x = copy(t)
    a = f**x
    b = a**2
    a = b*(f**2)
    a = a**2
    a = a*b
    a = a*f
    a = a.conjugate()
    b = a**q
    b = a*b
    a = a*b
    t0 = f**q
    t1 = t0*f
    t1 = t1**9
    a = t1*a
    t1 = f**4
    a = a*t1
    t0 = t0**2
    b = b*t0
    t0 = f**(q**2)
    b = b*t0
    t0 = b**x
    t1 = t0**2
    t0 = t1**2
    t0 = t0*t1
    t0 = t0**x
    t0 = t0*b
    a = t0*a
    t0 = f**(q**3)
    f = t0*a
    return f 

def final_exp_fuentes_castaneda(f: Fq12) -> Fq12:
    f = easy_part(f)
    t = Integer(4965661367192848881)
    x = copy(t)
    a = f**x
    a = a**2
    b = a**2
    b = a * b
    t = b**x
    tmp = f.conjugate()
    tmp = tmp**(q**3)
    f = f*tmp
    f = f * t
    b = b * t
    t = t**2
    t = t**x
    b = b * t
    tmp = a.conjugate()
    t = b * tmp
    tmp = t**(q**3)
    f = f * tmp
    tmp = t**q
    f = f * tmp
    f = f * b
    tmp = b**(q**2)
    f = f * tmp
    return f

EXPONENTIATION_TESTS_NUMBER = 1

print('Preparing the final exponentiation tests...')

tests_dict = {'tests': []}

for _ in range(EXPONENTIATION_TESTS_NUMBER):
    # Generating random value
    f = Fq12.random_element()
    f_exp = f^e

    assert f_exp**r == 1, 'final exponentiation must be in the r-th power unit subfield'

    assert final_exp(f) == f_exp, 'final exponentiation is wrong!'
    assert final_exp_devegili(f) == f_exp, 'final exponentiation using Devegili method is wrong!'

    tests_dict['tests'].append({
        'scalar': fq12_to_dictionary(f),
        'expected': fq12_to_dictionary(f_exp)
    })

print('Final exponentiation tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/ec_pairing/final_exp_tests.json'

print(f'Saving the final exponentiation tests to {FILE_NAME}...')

with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

# --- Pairing tests ---
PAIRING_TESTS_NUMBER = 1

print('Preparing the pairing tests...')

tests_dict = {'tests': []}

def miller_loop(P: G1, Q: G2):
    # --- Gathering coefficients step ---
    T = copy(Q)
    Q_negative = -copy(Q)
    f = Fq12.one()
    for i in reversed(range(1, len(SIX_U_PLUS_TWO_WNAF))):
        if i != len(SIX_U_PLUS_TWO_WNAF) - 1:
            f = f*f

        (c0, c3, c4), T2 = doubling_step(T, P)
        assert tuple_to_g2(T2) == 2*tuple_to_g2(T), 'Doubling step is wrong!'
        f = f * c0c3c4_to_fq12(c0, c3, c4)
        T = T2

        x = SIX_U_PLUS_TWO_WNAF[i-1]
        if x == 1:
            (c0, c3, c4), TQ = addition_step(Q, T, P)
            assert tuple_to_g2(TQ) == tuple_to_g2(T) + tuple_to_g2(Q), 'Addition step is wrong!'
            f = f * c0c3c4_to_fq12(c0, c3, c4)
            T = TQ
        elif x == -1:
            (c0, c3, c4), TQ = addition_step(Q_negative, T, P)
            assert tuple_to_g2(TQ) == tuple_to_g2(T) + Q_negative, 'Addition step is wrong!'
            f = f * c0c3c4_to_fq12(c0, c3, c4)
            T = TQ

    # Some additional steps to finalize the Miller loop...
    # Q1 <- pi_p(Q)
    Q1 = [Q[0], Q[1], Q[2]]
    Q1[0] = Q1[0].conjugate() * FROBENIUS_COEFF_FQ6_C1_1
    Q1[1] = Q1[1].conjugate() * XI_TO_Q_MINUS_1_OVER_2

    # Q2 <- -pi_{p^2}(Q)
    Q2 = [Q[0], Q[1], Q[2]]
    Q2[0] = Q2[0] * FROBENIUS_COEFF_FQ6_C1_2

    # Line evaluation at Q1
    (c0, c3, c4), TQ1 = addition_step(Q1, T, P)
    assert tuple_to_g2(TQ1) == tuple_to_g2(T) + tuple_to_g2(Q1), 'Addition step is wrong!'
    f = f * c0c3c4_to_fq12(c0, c3, c4)
    T = TQ1

    # Line evaluation at Q2
    (c0, c3, c4), TQ2 = addition_step(Q2, T, P)
    assert tuple_to_g2(TQ2) == tuple_to_g2(T) + tuple_to_g2(Q2), 'Addition step is wrong!'
    f = f * c0c3c4_to_fq12(c0, c3, c4)
    
    return f

def pairing(P, Q):
    f = miller_loop(P, Q)
    return f^e

for _ in range(PAIRING_TESTS_NUMBER):
    # Defining random elements
    a = Fq.random_element()
    A = a * G1_GEN

    b = Fq.random_element()
    B = b * G2_GEN

    pair = pairing(A, B)
    pair_AB = pairing(A, 2*B)
    pair_BA = pairing(2*A, B)

    assert pair_AB**r == pair_BA**r == pair**r == 1, "Pairing result is not in the rth roots of unity subgroup!"
    assert pair_BA == pair_AB == pair**2, "Pairing result is not correct!"

    tests_dict['tests'].append({
        'g1_point': g1_point_to_dictionary(A),
        'g2_point': g2_point_to_dictionary(B),
        'miller_loop': fq12_to_dictionary(miller_loop(A, B)),
        'pairing': fq12_to_dictionary(pairing(A, B))
    })

print('Pairing tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/ec_pairing/pairing_tests.json'

print(f'Saving the pairing tests to {FILE_NAME}...')

with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

# --- Invalid subgroup tests ---
INVALID_SUBGROUP_TESTS_NUMBER = 1

print('Preparing the invalid subgroup pairing tests...')

tests_dict = {'tests': []}

for _ in range(INVALID_SUBGROUP_TESTS_NUMBER):
    # Defining random elements
    a = Fq.random_element()
    A = a * G1_GEN
    assert r*A == G1((0, 1, 0)), "This point is not in the valid subgroup!"

    # This point is not in the valid subgroup (most likely!) since only
    # a narrow subset of G2 points actually satisfies [r]P = O
    B = G2.random_point()
    assert r*B != G2((0, 1, 0)), "This point should not be in the valid subgroup!"

    pair_AB = pairing(A, 2*B)
    pair_BA = pairing(2*A, B)

    assert pair_AB != pair_BA, "Bilinearity is satisfied for some reason!"

    tests_dict['tests'].append({
        'g1_point': g1_point_to_dictionary(A),
        'g2_point': g2_point_to_dictionary(B),
        'g1_point_doubled': g1_point_to_dictionary(2*A),
        'g2_point_doubled': g2_point_to_dictionary(2*B),
    })

# Saving the json file
FILE_NAME = '../json/ec_pairing/pairing_invalid_subgroup_tests.json'

print(f'Saving the invalid subgroup pairing tests to {FILE_NAME}...')

with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)