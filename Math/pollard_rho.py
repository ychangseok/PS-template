def gcd(a, b):
    while b != 0:
        a, b = b, a%b
    return a
def miller(n, a):
    if a % n == 0:
        return True
    k = n - 1
    while True:
        temp = pow(a, k, n)
        if temp == n - 1:
            return True
        if k % 2 == 1:
            return temp == 1 or temp == n - 1
        k //= 2
def prime(p):
    if p < 2:
        return False
    a = list()
    if p < 2047:
        a = [2]
    elif p < 1373653:
        a = [2, 3]
    elif p < 9080191:
        a = [31, 73]
    elif p < 25326001:
        a = [2, 3, 5]
    elif p < 3215031751:
        a = [2, 3, 5, 7]
    elif p < 4759123141:
        a = [2, 7, 61]
    else:
        a = [2, 13, 23, 1662803]
    #a = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    for i in a:
        if not miller(p, i):
            return False
    return True
def pollard_rho(n):
    import random
    if n == 1:
        return []
    if n % 2 == 0:
        return [2] + pollard_rho(n//2)
    if prime(n):
        return [n]
    d = 1
    x = random.randint(2, n)
    y = x
    c = random.randint(1, n)
    while d == 1:
        x = (x*x+c) % n
        y = (y*y+c) % n
        y = (y*y+c) % n
        d = gcd(abs(x-y), n)
        #print(x, y, d)
    return pollard_rho(d) + pollard_rho(n//d)
def factorization(n):
    b = pollard_rho(n)
    a = {}

    for i in b:
        if i in a.keys():
            a[i] += 1
        else:
            a[i] = 1

    c = []
    for i in a.keys():
        c.append([i, a[i]])

    c.sort()

    return c
def getDiv(n):
    f = factorization(n)
    div = []

    P = [a[0] for a in f]
    E = [range(a[1]+1) for a in f]

    for exps in product(*E):
        d = 1
        for (p, e) in zip(P, exps):
            d *= p**e 
        div.append(d)
    
    return div
