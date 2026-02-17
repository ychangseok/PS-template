def extgcd(a, b):
    # return [g, x, y] s.t. ax + by = gcd(a, b) = g

    if b == 0:
        return [a, 1, 0]
    g, x, y = extgcd(b, a%b)
    return [g, y, x - a//b * y]
def crt2(p1, p2):
    # x = p1[1] (mod p1[0])
    # x = p2[1] (mod p2[0])

    A, a = p1
    B, b = p2

    if a == -1:
        # no solution
        return [-1, -1]
    
    from math import gcd

    g = gcd(A, B)
    if a % g != b % g:
        return [-1, -1]

    g, u, v = extgcd(A, B)
    # uA + vB = g (mod AB)

    x = a*v*B + b*u*A
    x //= g
    x %= (A*B)//g

    return [(A*B)//g, x]
def crt(a):
    n = len(a)

    cur = a[0]
    for i in range(1, n):
        cur = crt2(cur, a[i])
    return cur
  
