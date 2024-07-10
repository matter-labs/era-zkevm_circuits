#! File for validating field extension arithmetic
import json

# --- Fq2 tests ---

# Defining the base prime field
q = 21888242871839275222246405745257275088696311157297823662689037894645226208583 # EC group order
Fq = GF(q) 

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

# Generating Fq2 tests
print('Preparing the Fq2 tests...')
tests_dict = {'tests': []}

FQ2_TESTS_NUMBER = 5

for _ in range(FQ2_TESTS_NUMBER):
    f = Fq2.random_element()
    g = Fq2.random_element()
    sum = f + g
    diff = f - g
    prod = f * g
    quot = f / g
    f_non_residue = f * (u + 9)
    frobenius_6 = f**(q**6)

    tests_dict['tests'].append({
        'scalar_1': fq2_to_dictionary(f),
        'scalar_2': fq2_to_dictionary(g),
        'expected': {
            'sum': fq2_to_dictionary(sum),
            'difference': fq2_to_dictionary(diff),
            'product': fq2_to_dictionary(prod),
            'quotient': fq2_to_dictionary(quot),
            'scalar_1_non_residue': fq2_to_dictionary(f_non_residue),
            'frobenius_6': fq2_to_dictionary(frobenius_6),
        }
    })

print('Fq2 tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/field_extensions/fq2_tests.json'

print(f'Saving the Fq6 tests to {FILE_NAME}...')
with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the Fq6 tests!')

# Generating Fq6 tests
print('Preparing the Fq6 tests...')
tests_dict = {'tests': []}

FQ6_TESTS_NUMBER = 1

for _ in range(FQ6_TESTS_NUMBER):
    # Defining inputs
    f = Fq6.random_element()
    g = Fq6.random_element()
    c0 = Fq2.random_element()
    c1 = Fq2.random_element()
    c2 = Fq2.random_element()
    h_c0c1 = c0 + c1*v
    h_c1 = c1*v
    h_c2 = c2*v^2

    # Defining the operations tested
    sum = f + g
    diff = f - g
    prod = f * g
    prod_c1 = f * h_c1
    prod_c0c1 = f * h_c0c1
    prod_c2 = f * h_c2
    f_inv = f.inverse()
    g_inv = g.inverse()
    quot = f / g
    f_square = f^2
    f_non_residue = f * v
    f_frobenius_1 = f^(q^1)
    g_frobenius_2 = g^(q^2)
    f_frobenius_3 = f^(q^3)

    tests_dict['tests'].append({
        'scalar_1': fq6_to_dictionary(f),
        'scalar_2': fq6_to_dictionary(g),
        'c0': fq2_to_dictionary(c0),
        'c1': fq2_to_dictionary(c1),
        'c2': fq2_to_dictionary(c2),
        'expected': {
            'sum': fq6_to_dictionary(sum),
            'difference': fq6_to_dictionary(diff),
            'product': fq6_to_dictionary(prod),
            'quotient': fq6_to_dictionary(quot),
            'product_c1': fq6_to_dictionary(prod_c1),
            'product_c0c1': fq6_to_dictionary(prod_c0c1),
            'product_c2': fq6_to_dictionary(prod_c2),
            'scalar_1_inverse': fq6_to_dictionary(f_inv),
            'scalar_1_square': fq6_to_dictionary(f_square),
            'scalar_1_non_residue': fq6_to_dictionary(f_non_residue),
            'scalar_1_frobenius_1': fq6_to_dictionary(f_frobenius_1),
            'scalar_2_frobenius_2': fq6_to_dictionary(g_frobenius_2),
            'scalar_1_frobenius_3': fq6_to_dictionary(f_frobenius_3),
        }
    })

print('Fq6 tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/field_extensions/fq6_tests.json'

print(f'Saving the Fq6 tests to {FILE_NAME}...')
with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the Fq6 tests!')

# --- Generating Fq12 tests ---
print('Preparing the Fq12 tests...')
tests_dict = {'tests': []}

FQ12_TESTS_NUMBER = 1
for _ in range(FQ12_TESTS_NUMBER):
    # Defining inputs
    f = Fq12.random_element()
    g = Fq12.random_element()

    # Defining sparse elements
    c0 = Fq2.random_element()
    c1 = Fq2.random_element()
    c3 = Fq2.random_element() 
    c4 = Fq2.random_element()
    c5 = Fq2.random_element()
    c0c1c4 = c0[0] + c0[1]*(W^6-9) + (c1[0]+c1[1]*(W^6-9))*W^2 + (c4[0]+c4[1]*(W^6-9))*W^3
    c0c3c4 = c0[0] + c0[1]*(W^6-9) + (c3[0]+c3[1]*(W^6-9))*W + (c4[0]+c4[1]*(W^6-9))*W^3
    c5v2w = (c5[0] + c5[1]*(W^6-9))*W^5

    # Defining the operations tested
    sum = f + g
    diff = f - g
    prod = f * g
    quot = f / g
    f_inv = f.inverse()
    f_square = f^2
    prod_c0c3c4 = f * c0c3c4
    prod_c0c1c4 = f * c0c1c4
    prod_c5v2w = f * c5v2w
    f_frobenius_1 = f^(q^1)
    g_frobenius_2 = g^(q^2)
    f_frobenius_3 = f^(q^3)
    pow_33 = f^(33)
    pow_67 = g^(67)
    pow_u = f^(4965661367192848881)
    pow_u2 = f^(4965661367192848881**2)
    pow_u3 = f^(4965661367192848881**3)

    tests_dict['tests'].append({
        'scalar_1': fq12_to_dictionary(f),
        'scalar_2': fq12_to_dictionary(g),
        'c0': fq2_to_dictionary(c0),
        'c1': fq2_to_dictionary(c1),
        'c3': fq2_to_dictionary(c3),
        'c4': fq2_to_dictionary(c4),
        'c5': fq2_to_dictionary(c5),
        'expected': {
            'sum': fq12_to_dictionary(sum),
            'difference': fq12_to_dictionary(diff),
            'product': fq12_to_dictionary(prod),
            'product_c0c3c4': fq12_to_dictionary(prod_c0c3c4),
            'product_c0c1c4': fq12_to_dictionary(prod_c0c1c4),
            'product_c5': fq12_to_dictionary(prod_c5v2w),
            'quotient': fq12_to_dictionary(quot),
            'scalar_1_inverse': fq12_to_dictionary(f_inv),
            'scalar_1_square': fq12_to_dictionary(f_square),
            'scalar_1_frobenius_1': fq12_to_dictionary(f_frobenius_1),
            'scalar_2_frobenius_2': fq12_to_dictionary(g_frobenius_2),
            'scalar_1_frobenius_3': fq12_to_dictionary(f_frobenius_3),
            'scalar_1_pow_33': fq12_to_dictionary(pow_33),
            'scalar_2_pow_67': fq12_to_dictionary(pow_67),
            'scalar_1_pow_u': fq12_to_dictionary(pow_u),
            'scalar_1_pow_u2': fq12_to_dictionary(pow_u2),
            'scalar_1_pow_u3': fq12_to_dictionary(pow_u3),
        }
    })

# Saving the fq12 tests
FILE_NAME = '../json/field_extensions/fq12_tests.json'
print(f'Saving the Fq12 tests to {FILE_NAME}...')
with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the Fq12 tests!')