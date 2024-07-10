from __future__ import annotations
import json

# Defining the base prime field
q = Integer(21888242871839275222246405745257275088696311157297823662689037894645226208583) # EC group order
Fq = GF(q) 

# r is taken from https://hackmd.io/@jpw/bn254
k = Integer(12) # Embedding degree
t = Integer(4965661367192848881)
r = Integer(21888242871839275222246405745257275088548364400416034343698204186575808495617)
e = (q^(12)-1)/r

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

def fq12_to_fq6_tuple(f: Fq12) -> tuple[Fq6, Fq6]:
    """
    Converts a Fq12 element to a tuple of Fq6 elements.
    """

    c0_c0 = (f[0] + 9*f[6]) + f[6] * u
    c0_c1 = (f[2] + 9*f[8]) + f[8] * u
    c0_c2 = (f[4] + 9*f[10]) + f[10] * u

    c1_c0 = (f[1] + 9*f[7]) + f[7] * u
    c1_c1 = (f[3] + 9*f[9]) + f[9] * u
    c1_c2 = (f[5] + 9*f[11]) + f[11] * u

    return (c0_c0 + c0_c1*v + c0_c2*v**2, c1_c0 + c1_c1*v + c1_c2*v**2)


def c0c3c4_to_fq12(c0: Fq2, c3: Fq2, c4: Fq2) -> Fq12:
    return c0[0] + c0[1]*(W^6-9) + (c3[0]+c3[1]*(W^6-9))*W + (c4[0]+c4[1]*(W^6-9))*W^3

def fq6_to_fq12(f: Fq6) -> Fq12:
    c0 = f[0]
    c1 = f[1]
    c2 = f[2]

    # Here 
    c0 = c0[0] + c0[1]*(W^6-9)
    c1 = c1[0] + c1[1]*(W^6-9)
    c2 = c2[0] + c2[1]*(W^6-9)

    # Here v = w^2 since Fq12 = Fq6[w]/(w^2 - v)
    return c0 + c1 * W^2 + c2 * W^4

class TorusWrapper:
    """
    Class for torus compression testing. Based on paper:
    https://eprint.iacr.org/2022/1162.pdf
    """

    def __init__(self, encoding: Fq6) -> None:
        """
        Encodes the given zeta in Fq12 to the T2 torus.
        """

        self._encoding = encoding

    @staticmethod
    def compress(zeta: Fq12) -> TorusWrapper:
        """
        Compresses the given zeta in Fq12 to the T2 torus.
        """

        c0, c1 = fq12_to_fq6_tuple(zeta)

        # booleans for exceptional cases
        c1_is_zero = c1 == 0
        c0_is_one = c0 == 1

        # Encoding the element
        encoding = (1 + c0 - 2*c0_is_one) / (c1 + c1_is_zero)
        return TorusWrapper(encoding)

    def decompress(self) -> Fq12:
        """
        Decompresses the element from T2 back to Fq12 using the formula:
        decoded = (encoding + w) / (encoding - w)
        """
        
        g = fq6_to_fq12(self._encoding)
        return (g + W) / (g - W)

    def mul(self, other: TorusWrapper) -> TorusWrapper:
        """
        Adds the element to itself.
        """

        # Reading encodings
        g1 = self._encoding
        g2 = other._encoding
        
        # Finding new encoding
        gamma = v
        flag = g1 + g2 == 0

        x = g1 * g2 + gamma
        y = g1 + g2

        encoding = (x - flag*x)/ (y + flag)
        return TorusWrapper(encoding)

    def inverse(self) -> TorusWrapper:
        """
        Inverts the element.
        """

        # Reading encodings
        g = self._encoding

        # Finding new encoding
        encoding = -g
        return TorusWrapper(encoding)
    
    def conjugate(self) -> TorusWrapper:
        """
        Conjugates the element.
        """

        return self.inverse()

    def square(self) -> TorusWrapper:
        """
        Squares the element.
        """

        # Reading encodings
        g = self._encoding

        # Finding new encoding
        gamma = v
        flag = g == 0
        encoding = (g + (gamma*(1-flag))/(g+flag))/2
        return TorusWrapper(encoding)

    def frob_map(self, i: Integer) -> TorusWrapper:
        """
        Applies the Frobenius map to the element.
        """

        # Reading encodings
        g = self._encoding

        # Finding new encoding
        gamma = v
        numerator = g**(q**i)
        denominator = gamma**((Integer(q)**i-1)//2)
        encoding = numerator / denominator
        return TorusWrapper(encoding)

    def pow_wnaf(self, decomposition: list[Integer]) -> TorusWrapper:
        """
        Applies the power to the element.
        """

        result = TorusWrapper.compress(Fq12.one())
        g = copy(self)
        g_inv = g.inverse()

        for bit in decomposition:
            result = result.square()

            if bit == 1:
                result = result.mul(g)
            elif bit == -1:
                result = result.mul(g_inv)

        return result

def random_easy_part_fq12() -> Fq12:
    """
    Returns the random fq12 being the result of an easy exponentiation part.
    """

    phi12 = lambda f: f**4 - f**2 + 1 # Cyclotomic polynomial of order 12
    f = Fq12.random_element()
    return f**((q**k-1) / phi12(q))

# Now, asserting that the class is written properly
VERIFICATION_TESTS_NUMBER = 10
for _ in range(VERIFICATION_TESTS_NUMBER):
    a = random_easy_part_fq12()
    b = random_easy_part_fq12()

    # Encoding the elements
    torus_a = TorusWrapper.compress(a)
    torus_b = TorusWrapper.compress(b)

    # Testing the decompression
    assert a == torus_a.decompress(), f'Decompression failed for a. \nExpected: {a}, \ngot: {torus_a.decompress()}'
    assert b == torus_b.decompress(), f'Decompression failed for b. \nExpected: {b}, \ngot: {torus_b.decompress()}'

    # Testing the multiplication
    assert a*b == torus_a.mul(torus_b).decompress(), f'Multiplication failed. \nExpected: {a*b}, \ngot: {torus_a.mul(torus_b).decompress()}'

    # Testing the inversion
    assert a.inverse() == torus_a.inverse().decompress(), f'Inversion failed. \nExpected: {a}, \ngot: {torus_a.inverse().mul(torus_a).decompress()}'

    # Testing the conjugation
    assert a.conjugate() == torus_a.conjugate().decompress(), f'Conjugation failed. \nExpected: {a.conjugate()}, \ngot: {torus_a.conjugate().decompress()}'

    # Testing the squaring
    assert a*a == torus_a.square().decompress(), f'Squaring failed. \nExpected: {a*a}, \ngot: {torus_a.square().decompress()}'

    # Testing the multiplication by 4
    assert a**4 == torus_a.pow_wnaf([1,0,0]).decompress(), 'Power 4 failed.'

    # Testing the multiplication by u
    u_decomposition = [
        1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 
        1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1
    ]
    #assert sum([k_i * 2**i for i, k_i in enumerate(u_decomposition)]) == t, 'Decomposition of u is invalid.'
    assert a**t == torus_a.pow_wnaf(u_decomposition).decompress(), 'Power u failed.'

    # Testing the Frobenius map
    for i in range(5):
        assert a**(q**i) == torus_a.frob_map(i).decompress(), f'Frobenius map failed. \nExpected: {a**(q**i)}, \ngot: {torus_a.frob_map(i).decompress()}'

print('All tests passed! Now we are ready to form the tests!')

# Generating the tests
print('Preparing the Torus tests...')
tests_dict = {'tests': []}

TORUS_TESTS_NUMBER = 1

for _ in range(TORUS_TESTS_NUMBER):
    a = random_easy_part_fq12()
    b = random_easy_part_fq12()

    # Encoding the elements
    torus_a = TorusWrapper.compress(a)
    torus_b = TorusWrapper.compress(b)

    # Finding encodings of all supported operations
    prod = torus_a.mul(torus_b)._encoding
    inverse = torus_a.inverse()._encoding
    conjugate = torus_a.conjugate()._encoding
    square = torus_a.square()._encoding
    frobenius_1 = torus_a.frob_map(1)._encoding
    frobenius_2 = torus_a.frob_map(2)._encoding
    frobenius_3 = torus_a.frob_map(3)._encoding
    pow_u = torus_a.pow_wnaf(u_decomposition)._encoding
    pow_13 = torus_a.pow_wnaf([1, 0, -1, 0, 1])._encoding

    tests_dict['tests'].append({
        'scalar_1': fq12_to_dictionary(a),
        'scalar_2': fq12_to_dictionary(b),
        'expected': {
            'encoding_1': fq6_to_dictionary(torus_a._encoding),
            'encoding_2': fq6_to_dictionary(torus_b._encoding),
            'product_encoding': fq6_to_dictionary(prod),
            'inverse_1_encoding': fq6_to_dictionary(inverse),
            'conjugate_1_encoding': fq6_to_dictionary(conjugate),
            'square_1_encoding': fq6_to_dictionary(square),
            'frobenius_1_encoding': fq6_to_dictionary(frobenius_1),
            'frobenius_2_encoding': fq6_to_dictionary(frobenius_2),
            'frobenius_3_encoding': fq6_to_dictionary(frobenius_3),
            'power_u_encoding': fq6_to_dictionary(pow_u),
            'power_13_encoding': fq6_to_dictionary(pow_13)
        }
    })

print('Torus tests formed successfully!')

# Saving the json file
FILE_NAME = '../json/algebraic_torus/torus_tests.json'

print(f'Saving the torus tests to {FILE_NAME}...')
with open(FILE_NAME, 'w') as f:
    json.dump(tests_dict, f, indent=4)

print('Successfully saved the Torus tests!')