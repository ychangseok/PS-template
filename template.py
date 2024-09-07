def roman_to_num(s):
    rom = {'I': 1, 'V': 5, 'X': 10, 'L': 50, 'C': 100, 'D': 500, 'M': 1000}
    int = 0
    for i in range(len(s)):
       if i > 0 and rom[s[i]] > rom[s[i - 1]]:
           int += rom[s[i]] - 2 * rom[s[i - 1]]
       else:
           int += rom[s[i]]
    return int
def num_to_roman(number):
    result = ""
    ints = [1000, 900, 500, 400, 100, 90, 50, 40, 10, 9, 5, 4, 1]
    roms = ["M", "CM", "D", "CD", "C", "XC", "L", "XL", "X", "IX", "V", "IV", "I"]
    for i in range(len(ints)):
        start = number // ints[i]
        result += roms[i] * start
        number -= ints[i] * start
    return result

def divide(a, b):
    if a >= 0:
        return a//b
    else:
        return -((-a)//b)
def gcd(a, b):
    while b != 0:
        a, b = b, a%b
    return a
def lcm(a, b):
    return (a*b)//gcd(a, b)
def gcd_rat(a, b, c, d):
    g = gcd(a*d, b*c)
    gg = gcd(g, b*d)
    ans = [g // gg, (b*d) // gg]
    return ans

# matrix things
def unit_matrix(n):
    # return n by n unit matrix
    ans = [[0]*n for _ in range(n)]
    for i in range(n):
        ans[i][i] = 1
    return ans
def matrix_plus(x, y, mod=0):
    n = len(x)
    ans = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            ans[i][j] = (x[i][j] + y[i][j])
            if mod:
                ans[i][j] %= mod
    return ans
def matrix_mul(mat1, mat2, mod=0):
    m = len(mat1)
    n = len(mat1[0])
    p = len(mat2)
    q = len(mat2[0])

    if n != p:
        print("Matrix mul error")
        exit()

    ans = [[0]*q for _ in range(m)]
    for i in range(m):
        for j in range(q):
            for k in range(n):
                ans[i][j] += mat1[i][k] * mat2[k][j]
            if mod:
                ans[i][j] %= mod
    return ans
def matrix_mod(x, mod):
    ans = list()
    for i in x:
        a = list()
        for j in i:
            if mod:
                a.append(j % mod)
            else:
                a.append(j)
        ans.append(a)
    return ans
def matrix_power(x, y, mod=0):
    n = len(x)
    res = unit_matrix(n)
    s = bin(y)[2:]
    for i in s:
        if ord(i) == 49:
            res = matrix_mul(res, res, mod)
            res = matrix_mul(res, x, mod)
            res = matrix_mod(res, mod)
        else:
            res = matrix_mul(res, res, mod)
            res = matrix_mod(res, mod)
    return res
def det(m, MOD):
    # m is n by n matrix
    # return det(m) mod MOD
    # by Gaussian elimination with pivoting

    n = len(m)
    cnt = 0

    for i in range(n):
        tmp = [[_, m[_][i]] for _ in range(i, n)]
        tmp.sort(key=lambda x: -abs(x[1]))
        i_max = tmp[0][0]

        if m[i_max][i] == 0:
            continue

        m[i], m[i_max] = m[i_max], m[i]
        if i != i_max:
            cnt += 1

        for j in range(i+1, n):
            mult = m[j][i] * pow(m[i][i], -1, MOD)
            mult %= MOD

            for k in range(i, n):
                m[j][k] += m[i][k]*(MOD - mult)
                m[j][k] %= MOD

    ans = 1
    for i in range(n):
        ans *= m[i][i]
        ans %= MOD

    if cnt % 2:
        ans = MOD - ans

    return ans % MOD

def transpose(a):
    n = len(a)
    return [[a[j][i] for j in range(n)] for i in range(n)]
def inv(a, MOD):
    n = len(a)
    b = [[a[_][i] if i<n else 0 for i in range(2*n)] for _ in range(n)]
    for j in range(n):
        b[j][j+n] = 1

    j = 0
    r = 0

    while j < 2*n and r < n:

        for i in range(r, n):
            if b[i][j]:
                b[i], b[r] = b[r], b[i]
                break

        if b[r][j]:
            B = b[r][j]
            for k in range(2*n):
                b[r][k] *= pow(B, -1, MOD)
                b[r][k] %= MOD

            for i in range(n):
                if i != r:
                    B = b[i][j]
                    for k in range(2*n):
                        b[i][k] += b[r][k]*(MOD-B)
                        b[i][k] %= MOD

            r += 1
        j += 1

    inva = [[b[i][j+n] for j in range(n)] for i in range(n)]
    return inva

def Hessenberg(m, mod=0):
    # m in n by n matrix
    # find upper Hessenberg matrix
    # that is similar to matrix m

    n = len(m)
    col = [i for i in range(n)]

    for j in range(n-2):
        for i in range(j+1, n):
            if m[i][col[j]]:
                m[i], m[j+1] = m[j+1], m[i]
                col[i], col[j+1] = col[j+1], col[i]
                break

        if m[j+1][col[j]]:
            for i in range(j+2, n):
                x = (mod-m[i][col[j]]) * pow(m[j+1][col[j]], -1, mod)
                x %= mod

                for k in range(n):
                    m[i][col[k]] += m[j+1][col[k]]*x
                    m[i][col[k]] %= mod
                for k in range(n):
                    m[k][col[j+1]] += (mod-m[k][col[i]])*x
                    m[k][col[j+1]] %= mod

    return m
def get_char_poly(m, mod=0):
    # return det(xI - m)
    n = len(m)
    b = Hessenberg(m, mod)

    # M = xI - m
    M = [[[b[i][j]] for j in range(n)] for i in range(n)]
    for i in range(n):
        M[i][i].append(mod-1)

    # det (M) = det(xI-m)
    dp = [[0] for _ in range(n+1)]
    dp[0] = [1]

    for k in range(1, n+1):

        tmp = 1
        for i in range(k-1, -1, -1):

            c = poly_multi(dp[i], [tmp], mod)

            if (k - 1 - i) % 2 == 1:
                c = poly_multi(c, [mod-1], mod)

            c = poly_multi(c, M[i][k-1], mod)

            dp[k] = poly_add(dp[k], c, mod)

            tmp *= M[i][i-1][0]
            tmp %= mod

    return dp[n]


def getnthfibo(n, mod):
    matrix = [[1, 1], [1, 0]]
    ans = matrix_power(matrix, n - 1, mod)
    return ans[0][0]

def sum_of_div(i):
    s = 0
    for j in range(1, i):
        if i % j == 0:
            s += j
    return s
def num_of_div(i):
    s = 0
    j = 1
    while j*j <= i:
        if i % j == 0:
            if j*j == i:
                s += 1
            else:
                s += 2
        j += 1
    return s

def base(n, b):
    if n < 0:
        return "-" + base(-n, b)

    letter = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!@#$%^&*()"
    s = ""
    #s = list()
    while True:
        s += letter[n % b]
        #s.append(a%n)
        n -= n % b
        if n == 0:
            break
        n //= b
    #s.reverse()
    s = s[::-1]
    return s
def base_inv(s, n):
    l = len(s)
    ans = 0
    for i in range(l):
        a = ord(s[i]) - 48
        if a > 9:
            a -= 7
        if a > 35:
            a -= 6
        if a >= n:
            return -1
        ans += a * (n**(l-1-i))
    return ans

def gcd(a, b):
    while b != 0:
        a, b = b, a%b
    return a
def power(x, y, mod=0):
    res = 1
    while y != 0:
        if y % 2 == 1:
            res *= x
            if mod:
                res %= mod
        y //= 2
        x *= x
        if mod:
            x %= mod
    if mod:
        res %= mod
    return res
def miller(n, a):
    if a % n == 0:
        return True
    k = n - 1
    while True:
        temp = power(a, k, n)
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
def phi(n):
    # with pollard_rho
    fact = factorization(n)

    ans = 1
    for [x, y] in fact:
        ans *= pow(x, y) - pow(x, y - 1)
    return ans
def num_of_div(n):
    # with pollard_rho
    a = factorization(n)
    ans = 1
    for [c, b] in a:
        ans *= b+1
    return ans
def merge_fact(a, b):
    # Given factorization of a and b, calculate factorization of a*b
    tmp = {}
    for i in a.keys():
        if i in tmp.keys():
            tmp[i] += a[i]
        else:
            tmp[i] = a[i]

    for i in b.keys():
        if i in tmp.keys():
            tmp[i] += b[i]
        else:
            tmp[i] = b[i]

    return tmp

def mod_inverse(x, mod):
    # Suppose x % mod != 0
    return power(x, mod-2, mod)
def power_tower_solve(a, n, mod):
    # calculate a[0]^(a[1]^...) % mod
    # n = len(a)
    # mod < 2**30

    if mod == 1:
        return 0

    if n == 0:
        return 1 % mod
    if n == 1:
        return a[0] % mod
    if n == 2:
        return power(a[0], a[1], mod)
    if n == 3 and (a[1:] in [[2, 2], [2, 3], [2, 4], [3, 2], [3, 3], [4, 2], [5, 2]]):
        return power(a[0], a[1] ** a[2], mod)
    if n == 4 and a[1:] == [2, 2, 2]:
        return power(a[0], 16, mod)

    pmod = phi(mod)
    return power(a[0], power_tower_solve(a[1:], n - 1, pmod) + 30 * pmod, mod)

def phi(n):
    a = {}
    i = 2

    if n == 1:
        return 1

    while i * i <= n:
        if n % i == 0:
            if i in a.keys():
                a[i] += 1
            else:
                a[i] = 1
            n //= i
            continue
        i += 1
    if n in a.keys():
        a[n] += 1
    else:
        a[n] = 1

    ans = 1
    for i in a.keys():
        ans *= pow(i, a[i]) - pow(i, a[i] - 1)
    return ans
def lucas(n, k, m):
    # comb(n, k) % m
    ans = 1
    while n or k:
        ans *= comb[n%m][k%m]
        n //= m
        k //= m
        ans %= m
    return ans


def poly_add(p1, p2, mod=0):
    # add to polynomial p1 & p2
    l1 = len(p1)
    l2 = len(p2)
    l = max(l1, l2)
    p = [0 for _ in range(l)]

    for i in range(l):
        if i < l1:
            p[i] += p1[i]
        if i < l2:
            p[i] += p2[i]
        p[i] %= mod

    return p
def poly_multi(p1, p2, mod=0):
    '''
    p1 = [1, 3] -> 1+3x
    p1 = [1, 1, 2] -> 1 +x+2xx
    '''
    d1 = len(p1)
    d2 = len(p2)
    d = d1 + d2 - 1

    ans = [0 for _ in range(d)]

    for i in range(d1):
        for j in range(d2):
            ans[i+j] += p1[i]*p2[j]
            ans[i+j] %= mod

    return ans
def evaluate(p, x, mod=0):
    # p : poly, x : int
    # return p(x)

    l = len(p)
    ans = p[l-1]
    for i in range(l-2, -1, -1):
        ans *= x
        ans += p[i]
        ans %= mod
    return ans
def poly_div(p1, p):
    # suppose p1 = (x^p - 1)g(x)
    # return p1 / (x^p - 1)
    # p2 = x^p - 1

    d1 = len(p1) - 1

    d = d1 - p

    ans = [0 for _ in range(d+1)]

    for i in range(d, -1, -1):
        ans[i] = p1[i+p]

        p1[i+p] -= ans[i]
        p1[i] += ans[i]

    return ans


def fact_mod_prime(n, p):
    # this method is useful when p is small

    # calculating n! % p
    # n! = M p + r
    # r < p
    # return [M, r]

    # fact[i] = i! % p
    # i < p

    if n < p:
        return[0, fact[n]]

    k, r = n // p, n % p
    K = fact_mod_prime(k)

    mod = p
    k_, r_ = n // mod, n % mod
    m_ = fact[r_]
    if k_ % 2 == 1:
        m_ = mod - m_

    m = m_ * K[1]
    m %= mod

    k += K[0]
    return [k, m]
def comb_mod_prime(n, k, p):
    # calculating nCk % p
    # returns [k, m] such that
    # nCk = p*k + m
    # 0 <= m < p

    a = fact_mod_prime(n, p)
    b = fact_mod_prime(k, p)
    c = fact_mod_prime(n-k, p)
    mod = p

    t = a[0] - b[0] - c[0]
    n = a[1] * pow(b[1], 17, mod) * pow(c[1], 17, mod)

    return [t, n]

def fact_mod_primetower(n, p, e):
    # this method is useful when p is small

    # n! = M p^e + r
    # r < p^e
    # return [M, r]

    # fact[i] = i! % p
    # i < p

    # val[i] = (\prod_{(n, p) = 1, n \in [1, i]} n) % p^e
    # 0 <= i < p^e

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
    # nCk % p^e
    a = fact_mod_primetower(n, p, e)
    b = fact_mod_primetower(k, p, e)
    c = fact_mod_primetower(n-k, p, e)
    mod = p**e

    t = a[0] - b[0] - c[0]
    n = a[1] * pow(b[1], 17, mod) * pow(c[1], 17, mod)

    ans = pow(p, t, mod)*n
    return ans % mod

def d_n(n, mod):
    # derangement
    d = [1, 0]

    for i in range(2, n+1):
        d.append(((i-1)*(d[-1] + d[-2]))%mod)

    return d[n]
def factorial(n, mod):
    ans = 1

    for i in range(2, n+1):
        ans *= i
        ans %= mod

    return ans

def leap_year(year):
    return year % 400 == 0 or (year % 4 == 0 and year % 100)
def finddate(year, mon, day):
    #year, mon, day = map(int, date.split("-"))
    month = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

    if leap_year(year):
        month[2] = 29

    cnt = 0
    for i in range(1, mon):
        cnt += month[i]
    cnt += day

    for i in range(0, year):
        if leap_year(i):
            cnt += 366
        else:
            cnt += 365

    return cnt
def day_to_date(n):
    year = 0
    while True:
        if leap_year(year):
            if n >= 366:
                n -= 366
            else:
                break
        else:
            if n >= 365:
                n -= 365
            else:
                break
        year += 1

    month = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

    if leap_year(year):
        month[2] = 29

    mon = 1
    while True:
        if n <= month[mon]:
            break
        n -= month[mon]
        mon += 1

    return [year, mon, n]

def nextTerm(n, a, b):
    d = pow(a, phi(b) - 1, b)

    d *= b - 1
    d %= b

    d += b * ((n - d) // b)
    c = (a * d + 1) // b
    return [c, d]
def farey(n, K):
    a, b = map(int, input().split())
    c, d = nextTerm(n, a, b)

    cnt = 0

    while c <= n:
        k = (n + b) // d
        a, b, c, d = c, d, k*c-a, k*d-b

        cnt += 1
        if cnt == K:
            print(f"{a} {b}")
            exit(0)
    print(-1)

def order(n, g):
    # return order of g in Zn
    phin = phi(n)
    fact = factorization(n)
    ans = phin

    for [p, k] in fact:
        tmp = phin
        for i in range(k):
            tmp //= p
            if pow(g, tmp, n) != 1:
                break
            ans //= p

    return ans
def carmichael_function(n):
    if n == 1:
        return 1

    fact = factorization(n)
    if len(fact) == 1:
        p, k = fact[0]
        if p == 2 and k >= 3:
            return pow(p, k-2)
        else:
            return pow(p, k-1)*(p-1)
    else:
        p, k = fact[0]
        l = len(fact)
        ans = pow(p, k-1)*(p-1)

        for i in range(1, l):
            p, k = fact[i]
            ans = lcm(ans, pow(p, k-1)*(p-1))

        return ans

def modular_sqrt(p, n):
    # find x s.t. x^2 = n (mod p) in O(log p^2)
    # p is odd prime
    # assume such x exists
    
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


def f(a):
    b = {}
    for i in a:
        if i in b.keys():
            b[i] += 1
        else:
            b[i] = 1

    c = [[i, b[i]] for i in b.keys()]
    return c

def ccw(p1, p2, p3):
    op = p1[0]*p2[1] + p2[0]*p3[1] + p3[0]*p1[1]
    op -= p1[1]*p2[0] + p2[1]*p3[0] + p3[1]*p1[0]
    return (op > 0) - (op < 0)
def comp(p1, p2):
    return p1[0] > p2[0] or (p1[0] == p2[0] and p1[1] > p2[1])
def isIntersect(p1, p2, p3, p4):
    ab = ccw(p1, p2, p3) * ccw(p1, p2, p4)
    cd = ccw(p3, p4, p1) * ccw(p3, p4, p2)

    if ab == 0 and cd == 0:
        if comp(p1, p2):
            p1, p2 = p2, p1
        if comp(p3, p4):
            p3, p4 = p4, p3

        return not comp(p3, p2) and not comp(p1, p4)

    return ab <= 0 and cd <= 0

def distance2D(p1, p2):
    # p1 : [x, y]
    # p2 : [x, y]
    # return square of euclidean distance between two point p1, p2

    return (p1[0] - p2[0]) ** 2 + (p1[1] - p2[1]) ** 2
def distance3D(p1, p2):
    # p1 : [x, y, z]
    # p2 : [x, y, z]
    # return square of euclidean distance between two point p1, p2

    return (p1[0]-p2[0])**2 + (p1[1]-p2[1])**2 + (p1[2]-p2[2])**2
def module(x, y):
    # x % y
    if y > 0:
        return x % y
    else:
        return abs(y) + x % y
def pisano_period(m):
    f0 = 0
    f1 = 1
    f2 = 1
    for i in range(m*m):
        f2 = (f0+f1) % m
        f0 = f1
        f1 = f2
        if f0 == 0 and f1 == 1:
            return i+1
def knapsack(W, wt, n, val):
    k = [[0]*(W+1) for _ in range(n+1)]
    for i in range(n+1):
        for w in range(W+1):
            if i == 0 or w == 0:
                k[i][w] = 0
            elif wt[i-1] <= w:
                k[i][w] = max(val[i-1]+k[i-1][w-wt[i-1]], k[i-1][w])
            else:
                k[i][w] = k[i-1][w]
    return k[n][W]
def convert(s, j):
    ans = ""
    for i in s:
        if 65 <= ord(i) <= 90:
            ans += chr(65+((ord(i)-65+j)%26))
        elif 97 <= ord(i) <= 122:
            ans += chr(97+((ord(i)-97+j)%26))
        else:
            ans += i
    return ans
def binary_search(arr, x):
    low = 0
    high = len(arr)
    while low < high:
        mid = (high + low) // 2
        if arr[mid] <= x:
            low = mid + 1
        else:
            high = mid
    return high - 1
def digital_root(n):
    ans = 0
    n = str(n)
    for i in n:
        ans += ord(i) - 48
    return ans
def most_common(a : list):
    b = {}
    for i in a:
        if i in b.keys():
            b[i] += 1
        else:
            b[i] = 1
    c = []
    m = max(b.values())
    for i in b.keys():
        if b[i] == m:
            c.append(i)
    c.sort()
    if len(c) == 1:
        return c[0]
    else:
        return c[1]

# merge_sort + counting inversion
def merge(A, tmp, p, q, r):
    i = p
    j = q
    k = p
    inv_count = 0

    while i <= q-1 and j <= r:
        if A[i] <= A[j]:
            tmp[k] = A[i]
            k += 1
            i += 1
        else:
            tmp[k] = A[j]
            k += 1
            j += 1
            inv_count += q-i

    while i <= q-1:
        tmp[k] = A[i]
        k += 1
        i += 1

    while j <= r:
        tmp[k] = A[j]
        k += 1
        j += 1

    i = p

    while i <= r:
        A[i] = tmp[i]
        i += 1

    return inv_count
def merge_sort(A, tmp, p, r):
    # sort A[p:r]
    # To sort full array, call merge_sort(A, 0, len(A)-1)
    inv_count = 0

    if p < r:
        q = (p+r)//2
        inv_count += merge_sort(A, tmp, p, q)
        inv_count += merge_sort(A, tmp, q+1, r)
        inv_count += merge(A, tmp, p, q+1, r)
    return inv_count

def mabangjin(n):
    ans = [[0]*n for _ in range(n)]
    if n % 2 == 1:
        x = 0
        y = n // 2

        for cnt in range(1, n * n + 1):
            ans[x][y] = cnt

            if cnt % n == 0:
                x += 1
            else:
                x -= 1
                y -= 1
                if x < 0:
                    x += n
                if y < 0:
                    y += n
    else:
        if n % 4 == 0:
            for i in range(n):
                for j in range(n):
                    if [i % 4, j % 4] in [[0, 0], [0, 3], [1, 1], [1, 2], [2, 1], [2, 2], [3, 0], [3, 3]]:
                        ans[i][j] = i * n + j + 1
                    else:
                        ans[i][j] = n * n - i * n - j
        else:
            N = n
            n = N // 4
            m = N // 2

            tmp = mabangjin(m)

            for i in range(m):
                for j in range(m):
                    ans[i][j] = tmp[i][j]

            for i in range(m, 2*m):
                for j in range(m):
                    ans[i][j] = 3*m*m + tmp[i-m][j]

            for i in range(m):
                for j in range(m, 2*m):
                    ans[i][j] = 2*m*m + tmp[i][j-m]

            for i in range(m, 2*m):
                for j in range(m, 2*m):
                    ans[i][j] = m*m + tmp[i-m][j-m]

            for j in range(n):
                for i in range(m):
                    ans[i+m][j], ans[i][j] = ans[i][j], ans[i+m][j]

            for j in range(N - n + 1, N):
                for i in range(m):
                    ans[i+m][j], ans[i][j] = ans[i][j], ans[i+m][j]

            ans[n][n-1], ans[m+n][n-1] = ans[m+n][n-1], ans[n][n-1]
            ans[n][n], ans[m+n][n] = ans[m+n][n], ans[n][n]

    return ans
def mabangjin_check(ans):
    tmp = []
    n = len(ans)
    for i in range(n):
        tmp.append(sum(ans[i]))

    for i in range(n):
        s = 0
        for j in range(n):
            s += ans[j][i]
        tmp.append(s)

    s = 0
    for i in range(n):
        s += ans[i][i]
    tmp.append(s)

    s = 0
    for i in range(n):
        s += ans[n - 1 - i][i]
    tmp.append(s)

    return len(list(set(tmp)))
def print_mabangjin(ans):
    for i in ans:
        print(" ".join(map(str, i)))

def count_lattice(k : Fraction, b: Fraction, n):
    if k < 0 or b < 0:
        count_lattice(-k, b + b.__abs__().__ceil__(), n)
    # count # of lattice point under
    # y = kx + b, 0 <= x < n, y > 0

    # count # of (x, y) such that 0 <= x < n,  0 < y <= kx + b

    fk = k.__floor__()
    fb = b.__floor__()
    cnt = 0

    if k >= 1 or b >= 1:
        cnt += ((fk * (n-1) + 2 * fb) * n) // 2
        k -= fk
        b -= fb

    t = k*n + b
    ft = t.__floor__()

    if ft >= 1:
        cnt += count_lattice(1/k, (t-ft)/k, ft)
    return cnt

# O(sqrt{n}) methods
def prime(n):
    if n < 2:
        return False

    j = 2
    while j * j <= n:
        if n % j == 0:
            return False
        j += 1
    return True
def factorize(n):
    a = {}
    i = 2
    while i*i <= n:
        while n % i == 0:
            if i in a.keys():
                a[i] += 1
            else:
                a[i] = 1
            n //= i
        i += 1
    if n > 1:
        if n in a.keys():
            a[n] += 1
        else:
            a[n] = 1

    b = []
    for i in a.keys():
        b.append([i, a[i]])
    return b

class Cube:
    u = []
    f = []
    l = []
    r = []
    b = []
    d = []

    def __init__(self, capital=False):
        if capital:
            self.u = ["W" for _ in range(9)]
            self.f = ["G" for _ in range(9)]
            self.l = ["O" for _ in range(9)]
            self.r = ["R" for _ in range(9)]
            self.b = ["B" for _ in range(9)]
            self.d = ["Y" for _ in range(9)]
        else:
            self.u = ["w" for _ in range(9)]
            self.f = ["g" for _ in range(9)]
            self.l = ["o" for _ in range(9)]
            self.r = ["r" for _ in range(9)]
            self.b = ["b" for _ in range(9)]
            self.d = ["y" for _ in range(9)]

    def get_input(self):
        a = []
        for i in range(9):
            a.append(list(map(str, input().split())))

        inp = [a[0] + a[1] + a[2], a[3][:3] + a[4][:3] + a[5][:3], a[3][3:6] + a[4][3:6] + a[5][3:6],
               a[3][6:9] + a[4][6:9] + a[5][6:9], a[3][9:] + a[4][9:] + a[5][9:], a[6] + a[7] + a[8]]
        self.u = inp[0]
        self.l = inp[1]
        self.f = inp[2]
        self.r = inp[3]
        self.b = inp[4]
        self.d = inp[5]

    def print_white_side(self):
        for i in range(3):
            for j in range(3):
                print(self.u[3*i+j], end='')
            print()

    def print_all(self):
        uu = self.u
        ff = self.f
        ll = self.l
        rr = self.r
        bb = self.b
        dd = self.d
        print("         {} {} {}".format(uu[0], uu[1], uu[2]))
        print("         {} {} {}".format(uu[3], uu[4], uu[5]))
        print("         {} {} {}".format(uu[6], uu[7], uu[8]))
        print("{} {} {} {} {} {} {} {} {} {} {} {}".format(ll[0], ll[1], ll[2], ff[0], ff[1], ff[2], rr[0], rr[1], rr[2], bb[0], bb[1], bb[2]))
        print("{} {} {} {} {} {} {} {} {} {} {} {}".format(ll[3], ll[4], ll[5], ff[3], ff[4], ff[5], rr[3], rr[4], rr[5], bb[3], bb[4], bb[5]))
        print("{} {} {} {} {} {} {} {} {} {} {} {}".format(ll[6], ll[7], ll[8], ff[6], ff[7], ff[8], rr[6], rr[7], rr[8], bb[6], bb[7], bb[8]))
        print("         {} {} {}".format(dd[0], dd[1], dd[2]))
        print("         {} {} {}".format(dd[3], dd[4], dd[5]))
        print("         {} {} {}".format(dd[6], dd[7], dd[8]))

    def L(self):
        ll = self.l
        uu = self.u
        bb = self.b
        ff = self.f
        dd = self.d

        ll[0], ll[2], ll[6], ll[8] = ll[6], ll[0], ll[8], ll[2]
        ll[1], ll[3], ll[5], ll[7] = ll[3], ll[7], ll[1], ll[5]
        uu[0], ff[0], dd[0], bb[8] = bb[8], uu[0], ff[0], dd[0]
        uu[6], ff[6], dd[6], bb[2] = bb[2], uu[6], ff[6], dd[6]
        uu[3], ff[3], dd[3], bb[5] = bb[5], uu[3], ff[3], dd[3]

    def L_prime(self):
        self.L()
        self.L()
        self.L()

    def U(self):
        ll = self.l
        uu = self.u
        bb = self.b
        ff = self.f
        rr = self.r

        uu[0], uu[2], uu[6], uu[8] = uu[6], uu[0], uu[8], uu[2]
        uu[1], uu[3], uu[5], uu[7] = uu[3], uu[7], uu[1], uu[5]
        ll[1], ff[1], rr[1], bb[1] = ff[1], rr[1], bb[1], ll[1]
        ll[0], ff[0], rr[0], bb[0] = ff[0], rr[0], bb[0], ll[0]
        ll[2], ff[2], rr[2], bb[2] = ff[2], rr[2], bb[2], ll[2]

    def U_prime(self):
        self.U()
        self.U()
        self.U()

    def F(self):
        ll = self.l
        uu = self.u
        ff = self.f
        dd = self.d
        rr = self.r

        ff[0], ff[2], ff[6], ff[8] = ff[6], ff[0], ff[8], ff[2]
        ff[1], ff[3], ff[5], ff[7] = ff[3], ff[7], ff[1], ff[5]
        uu[6], rr[0], dd[2], ll[8] = ll[8], uu[6], rr[0], dd[2]
        uu[8], rr[6], dd[0], ll[2] = ll[2], uu[8], rr[6], dd[0]
        uu[7], rr[3], dd[1], ll[5] = ll[5], uu[7], rr[3], dd[1]

    def F_prime(self):
        self.F()
        self.F()
        self.F()

    def D(self):
        ll = self.l
        bb = self.b
        ff = self.f
        dd = self.d
        rr = self.r

        dd[0], dd[2], dd[6], dd[8] = dd[6], dd[0], dd[8], dd[2]
        dd[1], dd[3], dd[5], dd[7] = dd[3], dd[7], dd[1], dd[5]
        ll[6], ff[6], rr[6], bb[6] = bb[6], ll[6], ff[6], rr[6]
        ll[8], ff[8], rr[8], bb[8] = bb[8], ll[8], ff[8], rr[8]
        ll[7], ff[7], rr[7], bb[7] = bb[7], ll[7], ff[7], rr[7]

    def D_prime(self):
        self.D()
        self.D()
        self.D()

    def R(self):
        uu = self.u
        bb = self.b
        ff = self.f
        dd = self.d
        rr = self.r

        rr[0], rr[2], rr[6], rr[8] = rr[6], rr[0], rr[8], rr[2]
        rr[1], rr[3], rr[5], rr[7] = rr[3], rr[7], rr[1], rr[5]
        ff[2], uu[2], bb[6], dd[2] = dd[2], ff[2], uu[2], bb[6]
        ff[8], uu[8], bb[0], dd[8] = dd[8], ff[8], uu[8], bb[0]
        ff[5], uu[5], bb[3], dd[5] = dd[5], ff[5], uu[5], bb[3]

    def R_prime(self):
        self.R()
        self.R()
        self.R()

    def B(self):
        ll = self.l
        uu = self.u
        bb = self.b
        dd = self.d
        rr = self.r

        bb[0], bb[2], bb[6], bb[8] = bb[6], bb[0], bb[8], bb[2]
        bb[1], bb[3], bb[5], bb[7] = bb[3], bb[7], bb[1], bb[5]
        uu[2], ll[0], dd[6], rr[8] = rr[8], uu[2], ll[0], dd[6]
        uu[0], ll[6], dd[8], rr[2] = rr[2], uu[0], ll[6], dd[8]
        uu[1], ll[3], dd[7], rr[5] = rr[5], uu[1], ll[3], dd[7]

    def B_prime(self):
        self.B()
        self.B()
        self.B()

    def solved(self):
        check_set = lambda x : len(set(x))

        a = 0
        a += check_set(self.l)
        a += check_set(self.u)
        a += check_set(self.r)
        a += check_set(self.f)
        a += check_set(self.b)
        a += check_set(self.u)

        return a==6

mon = {"January":1,
       "February":2,
       "March":3,
       "April":4,
       "May":5,
       "June":6,
       "July":7,
       "August":8,
       "September":9,
       "October":10,
       "November":11,
       "December":12}
month = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
num = [
    ["+---+",
     "|   |",
     "|   |",
     "+   +",
     "|   |",
     "|   |",
     "+---+"],
    ["    +",
     "    |",
     "    |",
     "    +",
     "    |",
     "    |",
     "    +"
     ],
    ["+---+",
     "    |",
     "    |",
     "+---+",
     "|    ",
     "|    ",
     "+---+"],
    ["+---+",
     "    |",
     "    |",
     "+---+",
     "    |",
     "    |",
     "+---+"],
    ["+   +",
     "|   |",
     "|   |",
     "+---+",
     "    |",
     "    |",
     "    +"],
    ["+---+",
     "|    ",
     "|    ",
     "+---+",
     "    |",
     "    |",
     "+---+"],
    ["+---+",
     "|    ",
     "|    ",
     "+---+",
     "|   |",
     "|   |",
     "+---+"],
    ["+---+",
     "    |",
     "    |",
     "    +",
     "    |",
     "    |",
     "    +"],
    ["+---+",
     "|   |",
     "|   |",
     "+---+",
     "|   |",
     "|   |",
     "+---+"],
    ["+---+",
     "|   |",
     "|   |",
     "+---+",
     "    |",
     "    |",
     "+---+"],
]

import random
print(chr(97 + random.randint(0, 25)))

