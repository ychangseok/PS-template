struct SCC{
    vector<vector<int> > graph;

    vector<int> d;
    vector<bool> finished;
    vector<int> Scc;
    int scc_index;
    int id;
    vector<vector<int> > SCCList;
    stack<int> st;
    int n;

    SCC (int n_){
        n = n_;
        init(n);
    }

    void addEdge(int u, int v){
        graph[u].push_back(v);
    }

    void init(int n_){
        n = n_;
        d.resize(n+1);
        finished.resize(n+1);
        Scc.resize(n+1);
        graph.resize(n+1);

        for (int i = 1; i <= n; i++){
            d[i] = 0;
            finished[i] = false;
            Scc[i] = 0;
            graph[i].clear();
        }
        SCCList.clear();
        scc_index = 0;
        id = 0;
    }

    int getscc(int u){
        d[u] = ++id;
        st.push(u);

        int parent = d[u];
        for (int v : graph[u]){
            if (d[v] == 0) parent = min(parent, getscc(v));
            else if (!finished[v]) parent = min(parent, d[v]);
        }

        if (parent == d[u]){
            vector<int> scc;

            while (true){
                int t = st.top(); st.pop();
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

    void getSCC(){
        for (int i = 1; i <= n; i++){
            if (d[i] == 0) getscc(i);
        }
    }
};
