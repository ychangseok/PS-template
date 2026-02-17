def modular_sqrt(p, n):
    # if p = 4k+3
    # then \pm n^{k+1} is modular sqrt

    # find x s.t. x^2 = n (mod p) in O(log p^2)
    # p is odd prime

    # O(log^2 p)

    if pow(n, (p-1)//2, p) == p-1:
        print("No modulo sqrt exists")
        assert False
    
    if p % 4 == 3:
        k = (p-3) // 4
        return pow(n, k+1, p)

    if n == 0:
        return 0
    
    Q = p - 1
    S = 0
    while Q % 2 == 0:
        Q //= 2
        S += 1

    z = 0
    while True:
        z = random.randint(1, p-1)
        if pow(z, (p-1)//2, p) != 1:
            break

    M = S
    c = pow(z, Q, p)
    t = pow(n, Q, p)
    R = pow(n, (Q+1)//2, p)

    while True:
        if t == 0:
            return 0
        if t == 1:
            return R

        i = 1
        while True:
            if pow(t, pow(2, i), p) == 1:
                break
            i += 1

        b = pow(c, pow(2, M-i-1), p)
        M = i
        c = pow(b, 2, p)
        t = (t*b*b)%p
        R = (R*b)%p
