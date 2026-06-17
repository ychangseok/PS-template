struct BipartiteUF{
    vector<int> par;
    vector<int> sz, c;
    vector<vector<int>> idx;
    int n;
    bool valid;
    
    BipartiteUF(int n_){
        n = n_;
        par.resize(n+1);
        sz.resize(n+1);
        c.resize(n+1);
        idx.resize(n+1);
        init();
    }
    
    void init(){
        for (int i = 1; i <= n; i++){
            par[i] = i;
            sz[i] = 1;
            c[i] = 0;
            idx[i] = vector<int>{i};
        }
        valid = true;
    }
    int get(int u){
        if (u == par[u]) return u;
        return par[u] = get(par[u]);
    }
    void merge(int u, int v, bool same){
        int uu = get(u);
        int vv = get(v);

        if (uu == vv){
            if (same) valid &= c[u] == c[v];
            else valid &= c[u] != c[v];
            return;
        }
        if (sz[uu] < sz[vv]) swap(uu, vv);

        par[vv] = uu;

        if (same && c[u] != c[v]){
            for (auto k : idx[vv]) c[k] = 1 - c[k];
        }else if (!same && c[u] == c[v]){
            for (auto k : idx[vv]) c[k] = 1 - c[k];            
        }

        sz[uu] += sz[vv];
        idx[uu].insert(idx[uu].end(), all(idx[vv]));
    }
    bool same(int u, int v){
        return get(u) == get(v);
    }
};
