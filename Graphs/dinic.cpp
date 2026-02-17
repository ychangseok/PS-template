struct Dinic {
	struct Edge {
		ll v, cap, cost;
	};

	vector<Edge> E;
    int edgecnt;

    int n;
    vector<vector<int> > g;

    Dinic(int n_){
        n = n_;
        init();
        g.resize(n+1);
        work.resize(n+1);
        check.resize(n+1);
    }

    void init(){
        g.clear();
        edgecnt = 0;
        E.clear();
    }

	void addEdge(int u, int v, ll cap=1, ll cost=0) {
        g[u].push_back(edgecnt);
        g[v].push_back(edgecnt+1);

        E.push_back({v, cap, cost});
        E.push_back({u, 0, -cost});
        edgecnt += 2;
	}
    void addBidirectionalEdge(int u, int v, ll cap=1, ll cost=0){
        g[u].push_back(edgecnt);
        g[v].push_back(edgecnt+1);

        E.push_back({v, cap, cost});
        E.push_back({u, cap, cost});
        edgecnt += 2;
    }

	bool spfa(int s, int t, vector<pair<int, int> >& parent, vector<ll>& d){
        fill(all(parent), make_pair(-1, -1));
        fill(all(d), 9e18);
        parent[s].first = -2;
        d[s] = 0;

        vector<bool> inQ(n+3, false);

        queue<int> q;
        q.push(s);
        inQ[s] = true;

        while (!q.empty()){
            int cur = q.front();
            q.pop();
            inQ[cur] = false;

            for (int nxt : g[cur]){
                int v = E[nxt].v;
                if (E[nxt].cap && d[cur] + E[nxt].cost < d[v]){
                    d[v] = d[cur] + E[nxt].cost;
                    parent[v] = {cur, nxt};

                    if (!inQ[v]){
                        q.push(v);
                        inQ[v] = true;
                    }
                }
            } 
        }  

        return parent[t].first != -1;
    }

    vector<bool> check;
    vector<int> work;
    
	ll dfs(int s, int t, int now, ll flow, const vector<ll> &d) {
		check[now] = true;
		if(now == t) return flow;

		for(; work[now] < g[now].size(); work[now]++) {
			auto &e = E[g[now][work[now]]];

			if(!check[e.v] && d[e.v] == d[now] + e.cost && e.cap) {
				ll ret = dfs(s, t, e.v, min(flow, e.cap), d);

				if (ret == 0) continue;
                
                e.cap -= ret;
                E[g[now][work[now]]^1].cap += ret;
                return ret;
			}
		}

		return 0;
	}

	pair<ll, ll> flow(int s, int t) {
        ll res = 0;
        ll flow = 0;
        vector<pair<int, int> > parent(n+3);
        vector<ll> d(n+3);
        
		while(spfa(s, t, parent, d)) {
            fill(all(check), false);
            fill(all(work), 0);
            
		    ll now = 0;
			while(now = dfs(s, t, s, 1e18, d)) {
				res += d[t] * now;
				flow += now;
                fill(all(check), false);
			}
		}

		return {flow, res};
	}

};
