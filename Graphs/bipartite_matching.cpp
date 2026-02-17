struct BipartiteMatching{
    int n, m;
    vector<vector<int> > graph;
    vector<int> amatch, bmatch;
    vector<int> vis;
    int visitcnt;

    BipartiteMatching(int n_, int m_){
        n = n_;
        m = m_;

        graph.resize(n+1, vector<int>());
        vis.resize(n+1, 0);
        visitcnt = 0;
    }

    void add(int u, int v){
        graph[u].push_back(v);
    }

    bool dfs(int u){
        if (vis[u] == visitcnt) return false;

        vis[u] = visitcnt;

        for (int v : graph[u]){
            if (bmatch[v] == -1 || dfs(bmatch[v])){
                amatch[u] = v;
                bmatch[v] = u;

                return true;
            }
        }
        return false;
    }
    int matching(){
        amatch = vector<int>(n+1, -1);
        bmatch = vector<int>(m+1, -1);

        int size = 0;
        for (int i = 1; i <= n; i++){
            visitcnt++;
            size += dfs(i);
        }
        return size;
    }

    void rdfs(int u, vector<bool> &check){
        if (check[u]) return;
        check[u] = true;
        for (auto v : graph[u]){
            check[v+n] = true;
            rdfs(bmatch[v], check);
        }
    }
    vector<int> getminVC(){
        matching();
        vector<bool> check(n+m+1, false);

        for (int i = 1; i <= n; i++){
            if (amatch[i] == -1) rdfs(i, check);
        }
        vector<int> res;

        for (int i = 1; i <= n; i++) {
            if (!check[i]) res.push_back(i);
        }
        for (int i = n+1; i <= n+m; i++){
            if (check[i]) res.push_back(i);
        }
        return res;
    }
    vector<int> getMIS(){
        matching();
        vector<bool> check(n+m+1, false);

        for (int i = 1; i <= n; i++){
            if (amatch[i] == -1) rdfs(i, check);
        }
        vector<int> res;

        for (int i = 1; i <= n; i++) {
            if (check[i]) res.push_back(i);
        }
        for (int i = n+1; i <= n+m; i++){
            if (!check[i]) res.push_back(i);
        }
        return res;
    }
};
