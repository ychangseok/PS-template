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
