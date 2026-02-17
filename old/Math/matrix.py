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
    while y:
        if y % 2 == 1: res = matrix_mul(res, x, mod)
        x = matrix_mul(x, x, mod)
        y //= 2
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
