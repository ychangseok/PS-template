struct UF{
    vector<int> par, sz;
    int n;
    
    UF(int n_){
        n = n_;
        par.resize(n+1);
        sz.resize(n+1);
        init();
    }
    
    void init(){
        for (int i = 1; i <= n; i++){
            par[i] = i;
            sz[i] = 1;
        }
    }
    int get(int u){
        if (u == par[u]) return u;
        return par[u] = get(par[u]);
    }
    void merge(int u, int v){
        u = get(u);
        v = get(v);

        if (u == v) return;
        if (u > v) swap(u, v);

        par[v] = u;
        sz[u] += sz[v];
    }
    int getsz(int u){
        return sz[get(u)];
    }
    bool same(int u, int v){
        return get(u) == get(v);
    }
};
