struct UFrollback{
    vector<int> par, sz, rank;
    int n;

    struct info{
        int u, v, pu, pv, szu, szv, ru, rv;
    };
    vector<info> trace;
    
    UFrollback(int n_){
        n = n_;
        par.resize(n+1);
        sz.resize(n+1);
        rank.resize(n+1);
        init();
        trace.clear();
    }
    
    void init(){
        for (int i = 1; i <= n; i++){
            par[i] = i;
            sz[i] = 1;
            rank[i] = 0;
        }
    }
    int get(int u){
        if (u == par[u]) return u;
        return get(par[u]);
    }
    void merge(int u, int v, bool perm=false){
        u = get(u);
        v = get(v);

        if (u == v) return;
        if (rank[v] > rank[u]) swap(u, v);

        if (!perm) trace.push_back({u, v, par[u], par[v], sz[u], sz[v], rank[u], rank[v]});

        par[v] = u;
        sz[u] += sz[v];
        rank[u] = max(rank[u], rank[v] + 1);
    }
    int getsz(int u){
        return sz[get(u)];
    }
    bool same(int u, int v){
        return get(u) == get(v);
    }

    void rollback(int SZ=0){
        while (trace.size() > SZ){
            info cur = trace.back();

            int u = cur.u;
            int v = cur.v;
            // par[u] = cur.pu;
            par[v] = cur.pv;
            sz[u] = cur.szu;
            rank[u] = cur.ru;
            // sz[v] = cur.szv;

            trace.pop_back();
        }
    }

};
