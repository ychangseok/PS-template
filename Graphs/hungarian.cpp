ll hungarian(const vector<vector<ll>> &cost){
    int n = cost.size() - 1;

    vector<ll> u(n+1);
    vector<ll> v(n+1);
    vector<int> p(n+1);
    vector<int> way(n+1);

    for (int i = 1; i <= n; i++){
        p[0] = i;
        int j0 = 0;
        vector<ll> minv(n+1, 1e18);
        vector<bool> used(n+1, false);

        do {
            used[j0] = true;
            int i0 = p[j0];
            ll delta = 1e18;
            int j1 = 0;

            for (int j = 1; j <= n; j++){
                if (!used[j]){
                    ll cur = cost[i0][j] - u[i0] - v[j];

                    if (cur < minv[j]){
                        minv[j] = cur;
                        way[j] = j0;
                    }

                    if (minv[j] < delta){
                        delta = minv[j];
                        j1 = j;
                    }
                }
            }

            for (int j = 0; j <= n; j++){
                if (used[j]){
                    u[p[j]] += delta;
                    v[j] -= delta;
                }else{
                    minv[j] -= delta;
                }
            }

            j0 = j1;
        }while (p[j0] != 0);

        do {
            int j1 = way[j0];
            p[j0] = p[j1];
            j0 = j1;
        }while (j0 != 0);
    }

    vector<int> match(n+1);
    for (int i = 1; i <= n; i++){
        match[p[i]] = i;
    }

    return -v[0];
}
