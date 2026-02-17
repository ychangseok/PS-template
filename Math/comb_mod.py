def fact_mod_prime(n, p):
    # this method is useful when p is small
    # O(log n)

    # n! = p^M r
    # return [M, r%p]

    # fact[i] = i! % p
    # i < p

    if n < p:
        return[0, fact[n]]

    k, r = n // p, n % p
    K = fact_mod_prime(k, p)

    k_, r_ = n // p, n % p
    m_ = fact[r_]
    if k_ % 2 == 1:
        m_ = p - m_

    m = m_ * K[1]
    m %= p

    k += K[0]
    return [k, m]
def comb_mod_prime(n, k, p):
    # nCk = p^M r
    # return [M, r % p]

    a = fact_mod_prime(n, p)
    b = fact_mod_prime(k, p)
    c = fact_mod_prime(n-k, p)

    t = a[0] - b[0] - c[0]
    n = a[1] * pow(b[1], -1, p) * pow(c[1], -1, p)

    return [t, n]

def fact_mod_primetower(n, p, e):
    # this method is useful when p is small
    # O(p^e + log n)

    # n! = p^M r
    # return [M, r % p^e]

    # fact[i] = i! % p, i < p
    # val[i] = (\prod_{(n, p) = 1, n \in [1, i]} n) % p^e, i < p^e

    if n < p:
        return[0, fact[n]]

    k, r = n // p, n % p
    K = fact_mod_primetower(k, p, e)

    mod = p**e
    k_, r_ = n // mod, n % mod
    m_ = val[r_]
    if k_ % 2 == 1:
        m_ = mod - val[r_]

    m = m_ * K[1]
    m %= mod

    k += K[0]
    return [k, m]
def comb_mod_primetower(n, k, p, e):
    # nCk = p^M r
    # return [M, r % p^e]
    a = fact_mod_primetower(n, p, e)
    b = fact_mod_primetower(k, p, e)
    c = fact_mod_primetower(n-k, p, e)
    mod = p**e

    t = a[0] - b[0] - c[0]
    n = a[1] * pow(b[1], -1, mod) * pow(c[1], -1, mod) % mod

    return [t, n]
