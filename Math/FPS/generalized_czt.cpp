Poly generalized_czt(FPS F, ll c, ll m){
    // return F(c^0), F(c^1), ..., F(c^m)

    int n = F.size();
    FPS C; C.resize(n+1);
    FPS D; D.resize(m+n);

    for (ll i = 1; i <= n; i++){
        C[i] = F[n-i] * Mint(c).pow((n-i)*(n-i-1)/2).inv();
    }
    for (ll i = 0; i < m+n; i++){
        D[i] = Mint(c).pow(i*(i-1)/2);
    }

    Poly ans(m+1);
    FPS B = C * D;
    for (ll i = 0; i <= m; i++){
        ans[i] = B[n+i] * Mint(c).pow(i*(i-1)/2).inv();
    }

    return ans;
}
