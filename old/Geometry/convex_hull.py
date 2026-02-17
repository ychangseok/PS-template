def convexhull(v):
    n = len(v)
    k = 0

    if n < 3:
        return v
    
    ans = [[] for _ in range(2*n)]
    v.sort()
    
    for i in range(n):
        while k >= 2 and ccw(ans[k-2], ans[k-1], v[i]) < 0:
            k -= 1
        ans[k] = v[i]
        k += 1
    t = k + 1
    for i in range(n-1, 0, -1):
        while k >= t and ccw(ans[k-2], ans[k-1], v[i-1]) < 0:
            k -= 1
        ans[k] = v[i-1]
        k += 1

    ans = ans[:k-1]
    return ans
