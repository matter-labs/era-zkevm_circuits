import json

Q = Integers(2**32)
R = Integers(2**256)
T = Integers(2**2048)

# File names for tests acoording to name (b,e,m): base, exponent, modulo in bytes

# --- 32-32-32 modular exponentiation tests ---
MODEXP_TESTS_NUMBER = 1 # How many tests to generate

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

print('Tests with 32-32-32 modexp formed successfully!')

# Saving the json file
MODEXP_FILE_NAME = './modexp_32-32-32_tests.json'
print(f'Saving the modexp tests to {MODEXP_FILE_NAME}...')

with open(MODEXP_FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the 32-32-32 modexp tests!')

# --- 32-4-32 modular exponentiation tests ---
MODEXP_TESTS_NUMBER = 1 # How many tests to generate

tests_dict = {'tests': []}

for _ in range(MODEXP_TESTS_NUMBER):
    # Picking random base, exponent and modulus
    base = Integer(R.random_element())
    exponent = Integer(Q.random_element())
    modulus = Integer(R.random_element())

    # Calculating the expected result
    expected = base.powermod(exponent, modulus)

    tests_dict['tests'].append({
        'base': f'0x{base.hex()}',
        'exponent': f'{exponent.hex()}',
        'modulus': f'0x{modulus.hex()}',
        'expected': f'0x{expected.hex()}'
    })

print('Tests with 32-4-32 modexp formed successfully!')

# Saving the json file
MODEXP_FILE_NAME = './modexp_32-4-32_tests.json'
print(f'Saving the modexp tests to {MODEXP_FILE_NAME}...')

with open(MODEXP_FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the 32-4-32 modexp tests!')

# --- 32-bit modular multiplication tests ---

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

print('Tests with 32-32 modmul formed successfully!')

# Saving the json file
MODMUL_FILE_NAME = './modmul_32-32_tests.json'
print(f'Saving the modmul tests to {MODMUL_FILE_NAME}...')
with open(MODMUL_FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the 32-32 modmul tests!')

# --- 256-byte modular multiplication tests ---
MODMUL256_TESTS_NUMBER = 1 # How many tests to generate

tests_dict = {'tests': []}

for _ in range(MODMUL256_TESTS_NUMBER):
    # Picking random a, b, and modulus
    a = Integer(T.random_element())
    b = Integer(T.random_element())
    modulus = Integer(T.random_element())

    # Decompose a into two 128-bit numbers
    a_low = a % (2**1024)
    a_high = a >> 1024
    assert a == a_low + a_high*2**1024, 'a was not decomposed correctly'

    # Decompose b into two 128-bit numbers
    b_low = b % (2**1024)
    b_high = b >> 1024
    assert b == b_low + b_high*2**1024, 'b was not decomposed correctly'

    def u2048_to_dict(x: Integer) -> dict:
        low, high = x % (2**1024), x >> 1024
        # Ok, now this is weird. 
        # Since we need the hex of fixed length (1024 bits), we need to add leading zeros
        # to the hex representation of the number.

        # Converting...
        low = low.hex()
        high = high.hex()

        # Adding leading zeros...
        low = '0'*(256 - len(low)) + low
        high = '0'*(256 - len(high)) + high

        return {
            'low': low,
            'high': high
        }

    # Calculating the expected result
    expected = (a * b) % modulus
    tests_dict['tests'].append({
        'a': u2048_to_dict(a),
        'b': u2048_to_dict(b),
        'modulus': u2048_to_dict(modulus),
        'expected': u2048_to_dict(expected)
    })

print('Tests formed successfully!')

# Saving the json file
MODMUL256_FILE_NAME = './modmul_256-256_tests.json'

print(f'Saving the modmul 256-256 tests to {MODMUL256_FILE_NAME}...')

with open(MODMUL256_FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the modmul 256-256 tests!')
