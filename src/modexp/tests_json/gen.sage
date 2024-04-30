import json

R = Integers(2**256)

# --- Modular exponentiation tests ---
MODEXP_TESTS_NUMBER = 10 # How many tests to generate

tests_dict = {'tests': []}

for _ in range(MODEXP_TESTS_NUMBER):
    # Picking random base, exponent and modulus
    base = Integer(R.random_element())
    exponent = Integer(R.random_element())
    modulus = Integer(R.random_element())

    # Calculating the expected result
    expected = base.powermod(exponent, modulus)

    tests_dict['tests'].append({
        'base': f'0x{base.hex()}',
        'exponent': f'0x{exponent.hex()}',
        'modulus': f'0x{modulus.hex()}',
        'expected': f'0x{expected.hex()}'
    })

print('Tests formed successfully!')

# Saving the json file
MODEXP_FILE_NAME = './modexp_tests.json'
print(f'Saving the modexp tests to {MODEXP_FILE_NAME}...')

with open(MODEXP_FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the modexp tests!')

# --- Modular multiplication tests ---

MODMUL_TESTS_NUMBER = 10 # How many tests to generate

tests_dict = {'tests': []}

for _ in range(MODMUL_TESTS_NUMBER):
    # Picking random a, b, and modulus
    a = Integer(R.random_element())
    b = Integer(R.random_element())
    modulus = Integer(R.random_element())

    # Calculating the expected result
    expected = (a * b) % modulus
    tests_dict['tests'].append({
        'a': f'0x{a.hex()}',
        'b': f'0x{b.hex()}',
        'modulus': f'0x{modulus.hex()}',
        'expected': f'0x{expected.hex()}'
    })

print('Tests formed successfully!')

# Saving the json file
MODMUL_FILE_NAME = './modmul_tests.json'
print(f'Saving the modmul tests to {MODMUL_FILE_NAME}...')
with open(MODMUL_FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the modmul tests!')
