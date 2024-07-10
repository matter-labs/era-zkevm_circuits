# Curve parameter u and the value of [log2(6x+2)] - 1:
u = 4965661367192848881
six_u_plus_2 = 6*u+2

six_u_plus_2_naf = [
    0, 0, 0, 1, 0, 1, 0, -1,
    0, 0, 1, -1, 0, 0, 1, 0,
    0, 1, 1, 0, -1, 0, 0, 1, 
    0, -1, 0, 0, 0, 0, 1, 1,
    1, 0, 0, -1, 0, 0, 1, 0, 
    0, 0, 0, 0, -1, 0, 0, 1,
    1, 0, 0, -1, 0, 0, 0, 1, 
    1, 0, -1, 0, 0, 1, 0, 1, 
    1]
print('\nCurve in WNAF format: {}', six_u_plus_2_naf)

# Verifying that the decomposition is indeed correct:
six_u_plus_2_wnaf = sum([k_i * 2**i for i, k_i in enumerate(six_u_plus_2_naf)])
assert six_u_plus_2_wnaf == six_u_plus_2

def to_wnaf(k: Integer) -> list[Integer]:
    """
    Converts an integer to its WNAF representation.
    """

    k = Integer(k)
    k_wnaf = []
    while k > 0:
        if k % 2 == 1:
            k_i = 2 - (k % 4)
            k -= k_i
        else:
            k_i = 0
        k //= 2
        k_wnaf.append(k_i)
    return k_wnaf

print('\nWNAF representation of 4: {}', to_wnaf(4))
print('\nWNAF representation of 13: {}', to_wnaf(13))
print('\nWNAF representation of u: {}', to_wnaf(u))
