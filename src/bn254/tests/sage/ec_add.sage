#! File for generating tests for testing elliptic curve addition
import json

TESTS_NUMBER = 10 # How many tests to generate

# Defining the curve
Fp = GF(21888242871839275222246405745257275088696311157297823662689037894645226208583)
E = EllipticCurve(Fp, [0, 3])
print(f'We use {E}')

# Generating tests
print('Preparing the tests...')
tests_dict = {'tests': []}
for _ in range(TESTS_NUMBER):
    A = E.random_point()
    B = E.random_point()
    C = A + B

    tests_dict['tests'].append({
        'point_1': {
            'x': str(A[0]), 
            'y': str(A[1])
        },
        'point_2': {
            'x': str(B[0]), 
            'y': str(B[1])
        },
        'expected': {
            'x': str(C[0]), 
            'y': str(C[1])
        }
    })

print('Tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/ec_add/ecadd_tests.json'

print(f'Saving the tests to {FILE_NAME}...')
with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the tests!')