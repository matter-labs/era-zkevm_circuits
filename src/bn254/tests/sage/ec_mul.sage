#! File for generating tests for testing elliptic curve multiplication
import json

# --- Decomposition Tests generation ---

# Defining the curve
p = 21888242871839275222246405745257275088696311157297823662689037894645226208583 # Finite field order
q = 21888242871839275222246405745257275088548364400416034343698204186575808495617 # EC group order
Fp = GF(p) # Finite field
Fq = GF(q) # EC group
E = EllipticCurve(Fp, [0, 3])
print(f'We use {E}')

# --- GLV Parameters ---
# Lambda parameter
lambd = 4407920970296243842393367215006156084916469457145843978461

# Defining vectors (a1,b1) and (a2,b2)
a1 = 0x89d3256894d213e3
b1 = -0x6f4d8248eeb859fc8211bbeb7d4f1128
a2 = 0x6f4d8248eeb859fd0be4e1541221250b
b2 = 0x89d3256894d213e3

# Precomputed b1/n and b2/n times 2**256
g1 = 0x24ccef014a773d2cf7a7bd9d4391eb18d
g2 = 0x2d91d232ec7e0b3d7

# Decomposition using precomputed g1 and g2
def decompose_aztec(k: Integer):
    c1 = (g2 * k) >> 256
    c2 = (g1 * k) >> 256

    q1 = c1 * b1
    q2 = -c2 * b2

    k2 = q2 - q1
    k2_lambda = k2 * lambd % q
    k1 = k - k2_lambda

    return k1, k2

# Generating tests...
DECOMPOSITION_TESTS_NUMBER = 10
print('Preparing the decomposition tests...')
tests_dict = {'tests': []}

for _ in range(DECOMPOSITION_TESTS_NUMBER):
    # Decomposing the scalar
    k = Integer(Fp.random_element())
    k1, k2 = decompose_aztec(k)

    # Making sure that k1 and k2 are in the field
    k = Fq(k)
    k1 = Fq(k1)
    k2 = Fq(k2)
    
    # Validating that tests generated are valid
    assert k == k1 + k2 * Fq(lambd)

    # Choosing between ki and -ki
    k1_negated, k2_negated = False, False
    if k1 > 2**128:
        k1 = -k1
        k1_negated = True
    
    if k2 > 2**128:
        k2 = -k2
        k2_negated = True

    assert (-1)**k1_negated*k1 + (-1)**k2_negated*k2*Fq(lambd) == k

    tests_dict['tests'].append({
        'k': str(k),
        'k1': str(k1),
        'k1_negated': k1_negated,
        'k2': str(k2),
        'k2_negated': k2_negated
    })

print('Decomposition tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/ec_mul/decomposition_tests.json'

print(f'Saving the decomposition tests to {FILE_NAME}...')
with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the decomposition tests!')

# --- Multiplication Tests generation ---

# Generating tests...
MULTIPLICATION_TESTS_NUMBER = 1
print('Preparing the multiplication tests...')
tests_dict = {'tests': []}

for _ in range(MULTIPLICATION_TESTS_NUMBER):
    # Generating random points
    P = E.random_point()
    k = Fq.random_element()
    Q = k * P

    tests_dict['tests'].append({
        'point': {
            'x': str(P[0]), 
            'y': str(P[1])
        },
        'scalar': str(k),
        'expected': {
            'x': str(Q[0]), 
            'y': str(Q[1])
        }
    })

print('Multiplication tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/ec_mul/ecmul_tests.json'

print(f'Saving the multiplication tests to {FILE_NAME}...')
with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the multiplication tests!')