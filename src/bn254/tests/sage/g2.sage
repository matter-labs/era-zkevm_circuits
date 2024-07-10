import json

# Defining the base prime field
q = 21888242871839275222246405745257275088696311157297823662689037894645226208583 # EC group order
Fq = GF(q) 

# Defining the extensions
K2.<x> = PolynomialRing(Fq)
Fq2.<u> = Fq.extension(x^2+1)

# Defining the G2 Curve
b = 3 / (u + 9)
E = EllipticCurve(Fq2, [0, b])

G2_TESTS_NUMBER = 2
print('Preparing the G2 Curve tests...')
tests_dict = {'tests': []}

for _ in range(G2_TESTS_NUMBER):
    # Generating two random points
    P = E.random_point()
    Q = E.random_point()

    # Finding expected values to check
    sum = P + Q
    P_double = P + P
    Q_double = Q + Q

    point_to_dictionary = lambda point : {
        'x': {
            'c0': str(point[0][0]), 
            'c1': str(point[0][1])
        }, 
        'y': {
            'c0': str(point[1][0]), 
            'c1': str(point[1][1])
        }
    }

    # Adding the test to the dictionary
    tests_dict['tests'].append({
        'point_1': point_to_dictionary(P),
        'point_2': point_to_dictionary(Q),
        'expected': {
            'sum': point_to_dictionary(sum),
            'point_1_double': point_to_dictionary(P_double),
            'point_2_double': point_to_dictionary(Q_double)
        }
    })

print('G2 Curve tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/ec_pairing/g2_tests.json'

print(f'Saving the G2 Curve tests to {FILE_NAME}...')

with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)