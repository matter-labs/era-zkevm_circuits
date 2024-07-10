import json

# Defining the base prime field
q = Integer(21888242871839275222246405745257275088696311157297823662689037894645226208583) # EC group order
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

# Converts the Fq number to 4 64-bit limbs in Montgomery form
def to_montgomery_limbs(number: Fq):
    number = Fq(number) * Fq(2^(256))
    number = Integer(number)

    # Building limbs
    limb_1 = number % 2**64
    limb_2 = (number // 2**64) % 2**64
    limb_3 = (number // 2**128) % 2**64
    limb_4 = (number // 2**192) % 2**64

    return [limb_1, limb_2, limb_3, limb_4]

def print_montgomery_limbs(number: Fq):
    limbs = to_montgomery_limbs(number)
    print([Integer(limb).hex() for limb in limbs])

# Finding inverse of an Fq12 element 0+1*w:
w = 0 + 1*W
w_inv = w.inverse()
assert w*w_inv == 1, 'inverse of w was found incorrectly'

w_inv_dict = fq12_to_dictionary(w_inv)
print(f'w^(-1) = {w_inv_dict}')

# Printing individual coefficients as montgomery limbs
# to further use as constants in the code
c2_c3_c0 = w_inv_dict['c1']['c2']['c0']
c2_c3_c1 = w_inv_dict['c1']['c2']['c1']
print_montgomery_limbs(c2_c3_c0)
print_montgomery_limbs(c2_c3_c1)

# Finding the inverse of two:
two = Fq12(2)
two_inv = two.inverse()
assert two*two_inv == 1, 'inverse of 2 was found incorrectly'

two_inv_dict = fq12_to_dictionary(two_inv)
print(f'2^(-1) = {two_inv_dict}')

c0 = two_inv_dict['c0']['c0']['c0']
print_montgomery_limbs(c0)