void ntt(vector<ll> &P, bool inverse, ll g, const ll mod){
    int n = P.size();
    if (n == 1) return;

    ll unit = g;
    if (inverse) unit = power(g, mod-2, mod);

    vector<ll> even, odd;
    for (int i = 0; i < n; i++){
        if (i % 2 == 0) even.push_back(P[i]);
        else            odd.push_back(P[i]);
    }

    ntt(even, inverse, (g*g)%mod, mod);
    ntt(odd, inverse, (g*g)%mod, mod);

    ll w = 1;
    for (int i = 0; i < n/2; i++){
        P[i] = even[i] + w * odd[i];
        P[i+n/2] = even[i] + (mod - w) * odd[i];
        P[i] %= mod;
        P[i+n/2] %= mod;
        w *= unit;
        w %= mod;
    }
}
