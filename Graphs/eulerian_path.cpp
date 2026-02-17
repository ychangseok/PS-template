vector<int> eulerian_path(){
    int v1 = -1, v2 = -1;
    vector<int> res;

    for (int i = 1; i <= 2*n; i++){
        if (deg[i] & 1){
            if (v1 == -1) v1 = i;
            else if (v2 == -1) v2 = i;
            else return res;
        }
    }

    if (v1 != -1){
        g[v1].insert(v2);
        g[v2].insert(v1);
        deg[v1]++;
        deg[v2]++;
    }

    int first = 0;
    for (int i = 1; i <= 2*n; i++){
        if (deg[i]){
            first = i;
            break;
        }
    }
    if (v1 != -1) first = v1;

    if (first == 0) return res;

    // cout << first << ' ' << v1 << ' ' << v2 << endl;

    stack<int> st;
    st.push(first);

    while (!st.empty()){
        int v = st.top();
        
        if (g[v].empty()){
            res.push_back(v);
            st.pop();
        }else{
            int i = (*g[v].begin());
            g[v].erase(g[v].find(i));
            g[i].erase(g[i].find(v));
            st.push(i);
        }
    }

    if (v1 != -1){
        for (int i = 0; i+1 < res.size(); i++){
            if (res[i] == v1 && res[i+1] == v2){
                vector<int> res2;
                for (int j = i+1; j < res.size(); j++){
                    res2.push_back(res[j]);
                }
                for (int j = 1; j <= i; j++){
                    res2.push_back(res[j]);
                }
                res = res2;
                break;
            }
            if (res[i] == v2 && res[i+1] == v1){
                vector<int> res2;
                for (int j = i+1; j < res.size(); j++){
                    res2.push_back(res[j]);
                }
                for (int j = 1; j <= i; j++){
                    res2.push_back(res[j]);
                }
                res = res2;
                break;
            }
        }
    }

    for (int i = 1; i <= 2*n; i++){
        if (g[i].size()){
            res.clear();
            return res;
        }
    }

    return res;
}
