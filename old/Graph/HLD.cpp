int dep[MAX], par[MAX], sz[MAX], in[MAX], out[MAX], top[MAX];
ll idx = 0;
vector<int> adj[MAX]; // adj list
vector<int> graph[MAX];

void dfs(int v=1, int prev=-1){
    for (int u : adj[v]){
        if (u == prev) continue;

        graph[v].push_back(u);
        dfs(u, v);
    }
}
void dfs1(int v=1){
    sz[v] = 1;

    for (int &u : graph[v]){
        dep[u] = dep[v] + 1;
        par[u] = v;
        dfs1(u);
        sz[v] += sz[u];

        if (sz[u] > sz[graph[v][0]]) swap(u, graph[v][0]);
    }
}
void dfs2(int v=1){
    in[v] = ++idx;
    for (int u : graph[v]){
        top[u] = (u == graph[v][0]) ? top[v] : u;
        dfs2(u);
    }
    out[v] = idx;
}
vector<array<int, 2>> getPath(int u, int v){
    vector<array<int, 2>> path;

    while (top[u] != top[v]){
        if (dep[top[u]] < dep[top[v]]) swap(u, v);

        ll xx = top[u];
        path.push_back({in[xx], in[u]});
        u = par[xx];
    }

    if (dep[u] > dep[v]) swap(u, v);
    path.push_back({in[u], in[v]});

    return path;
}
