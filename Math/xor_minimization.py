def xor_minimization(a):
    basis = []
    for k in a:
        for b in basis:
            k = min(k, b^k)
        if k: basis.append(k)

    if len(basis) == len(a):
        return min(basis)
    else:
        return 0
