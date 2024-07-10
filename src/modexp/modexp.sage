# Modexp helper file.
# Note that we use w = 64 so that n = 4. 

UINT4096_LIMBS_NUMBER = 128
UINT2048_LIMBS_NUMBER = 64
UINT512_LIMBS_NUMBER = 16
UINT256_LIMBS_NUMBER = 8
BASE = 2^(32) # UINT32 base

def gen_random_uint(limbs_number: int) -> list[Integer]:
    """
    Generated a random uint512 number represented by 64 uint8 limbs.
    """

    return [randint(0, BASE-1) for _ in range(limbs_number)]

def convert_from_limbs(limbs: list[Integer]) -> Integer:
    """
    Converts a list of uint8 limbs to an Integer.
    """
    
    return sum([limbs[i] * BASE^i for i in range(len(limbs))])

def long_division_u256(n: list[Integer], m: list[Integer]) -> (Integer, Integer):
    """
    Performs long division on two numbers in u256 represented by their limbs.
    """

    k = UINT512_LIMBS_NUMBER
    l = UINT256_LIMBS_NUMBER
    m = convert_from_limbs(m)

    # q <- 0, r <- first l-1 digits of n
    q = 0
    #r = convert_from_limbs([n[k-l+1+i] if i < l-1 else Integer(0) for i in range(k)])
    r = n[8:]
    r[0] = 0
    r[0:7] = r[1:8]
    r[7] = 0

    r = convert_from_limbs(r)

    # Initialize current d - intermediate dividend
    for i in range(k-l+1):
        # d_i <- b*r_{i-1} + \alpha_{i+l-1}
        d = r * BASE + n[k-l-i]

        # beta_i <- next digit of quotient
        # Using binary search to find beta_i
        left, right = 0, BASE
        for _ in range(33):
            beta = (right + left) // 2 + (right + left) % 2
            r = d - m * beta     
            if r < 0:
                right = beta - 1
            if r >= m:
                left = beta + 1
        
        assert 0 <= r < m, 'r was not in the range [0, m)'

        # q_i <- b*q_{i-1} + beta_i
        q = q * BASE + beta

    return (q, r)

def long_division_u2048(n: list[Integer], m: list[Integer]) -> (Integer, Integer):
    """
    Performs long division on two numbers represented by their limbs.
    """

    k = UINT512_LIMBS_NUMBER
    l = UINT256_LIMBS_NUMBER
    m = convert_from_limbs(m)

    # q <- 0, r <- first l-1 digits of n
    q = 0
    #r = convert_from_limbs([n[k-l+1+i] if i < l-1 else Integer(0) for i in range(k)])
    r = n[8:]
    r[0] = 0
    r[0:7] = r[1:8]
    r[7] = 0

    r = convert_from_limbs(r)

    # Initialize current d - intermediate dividend
    for i in range(k-l+1):
        # d_i <- b*r_{i-1} + \alpha_{i+l-1}
        d = r * BASE + n[k-l-i]

        # beta_i <- next digit of quotient
        # Using binary search to find beta_i
        left, right = 0, BASE
        for _ in range(33):
            beta = (right + left) // 2 + (right + left) % 2
            r = d - m * beta     
            if r < 0:
                right = beta - 1
            if r >= m:
                left = beta + 1
        
        assert 0 <= r < m, 'r was not in the range [0, m)'

        # q_i <- b*q_{i-1} + beta_i
        q = q * BASE + beta

    return (q, r)
    
def modexp(base: Integer, exponent: Integer, modulus: Integer) -> Integer:
    """
    Computes base^exponent mod modulus.
    """

    a = 1
    binary_exponent = exponent.binary()
    for i in range(len(binary_exponent)):
        a = a*a % modulus
        if Integer(binary_exponent[i]) % 2 == 1:
            a = a*base % modulus

    return a

# Verification tests
print('Starting verification tests for u512/u256 division...')
VERIFICATION_TESTS_NUMBER = 10
for i in range(VERIFICATION_TESTS_NUMBER):
    n = gen_random_uint(UINT512_LIMBS_NUMBER)
    m = gen_random_uint(UINT256_LIMBS_NUMBER)
    q, r = long_division_u256(n, m)
    
    n = convert_from_limbs(n)
    m = convert_from_limbs(m)
    
    assert q == n // m
    assert r == n % m
    
    b = 0xbbe4922f210aa886cc084106178a3e2e9048d0223acb60f55b0a0ad1458dda6a
    e = 0x590298d43998ff77a6b85f70835748739f57bed0e0ef16aec7ba2628da373cc7
    m = 0x4715ccf06b9b5602917948ec337e272e7515c3002b56f3a6324546e4c0c2410

    assert b.powermod(e, m) == modexp(b, e, m)

print('Verification tests for u512/u256 division have passed!...')


# Debugging
def modexp(base: Integer, exponent: Integer, modulus: Integer) -> Integer:
    """
    Computes base^exponent mod modulus.
    """

    a = 1
    binary_exponent = exponent.binary()
    print(binary_exponent)
    for i in range(len(binary_exponent)):
        a = a*a % modulus
        if Integer(binary_exponent[i]) % 2 == 1:
            a = a*base % modulus
        print('a=',a)
    return a

assert modexp(0xf3bc340d206ac21e61e505d2755dea8495430f7b76223cc2a2a8c8ddd276a475, 
    0x516470d4, 
    0xea0b9bc7558ba1b3c3b0dc4ba64adc399e31204f2649bc276bb0f4b056636d18) == 0xafe13a3215873fc72e28b2d45b6d986a1ec272ecabb86a9f8345e720a868ec61

            
