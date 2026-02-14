// SCC (Tarjan's algorithm)
ll d[MAX+3]; // 방문 순서
bool finished[MAX+3]; 
ll Scc[MAX+3]; // scc index
ll scc_index = 0;
ll id = 0;
vector<vector<ll> > SCCList;
stack<ll> st;

ll SCC(ll u){
    d[u] = ++id;

    st.push(u);

    ll parent = d[u];
    for (ll v : graph[u]){
        if (d[v] == 0) parent = min(parent, SCC(v));
        else if (!finished[v]) parent = min(parent, d[v]);
    }

    if (parent == d[u]){
        vector<ll> scc;

        while (true){
            ll t = st.top(); st.pop();
            scc.push_back(t);
            finished[t] = true;
            Scc[t] = scc_index;
            
            
            if (t == u) break;
        }

        SCCList.push_back(scc);
        scc_index++;
    }

    return parent;
}

void makeEdge(ll u, ll v){
    if (u > 0 && v > 0){
        graph[u+V].push_back(v);
        graph[v+V].push_back(u);
    } else if (u > 0 && v < 0){
        graph[u+V].push_back(V-v);
        graph[-v].push_back(u);
    } else if (u < 0 && v > 0){
        graph[-u].push_back(v);
        graph[V+v].push_back(V-u);
    } else if (u < 0 && v < 0){
        graph[-u].push_back(V-v);
        graph[-v].push_back(V-u);
    }
}
