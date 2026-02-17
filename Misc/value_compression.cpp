vector<ll> value_compression(const vector<ll> &v){
    vector<pair<ll, ll>> w;
    int n = v.size();
    for (int i = 0; i < n; i++){
        w.push_back({i, v[i]});
    }

    sort(all(w),
        [](pair<ll, ll> p1, pair<ll, ll> p2) -> bool{
            return p1.second < p2.second;
        }
    );


    ll cur = w[0].second;
    ll idx = 1;
    w[0].second = 1;

    for (int i = 1; i < n; i++){
        if (w[i].second == cur){
            w[i].second = idx;
        }else{
            idx++;
            cur = w[i].second;
            w[i].second = idx;
        }
    }

    sort(all(w),
        [](pair<ll, ll> p1, pair<ll, ll> p2) -> bool{
            return p1.first < p2.first;
        }
    );

    vector<ll> x;
    for (int i = 0; i < n; i++){
        x.push_back(w[i].second);
    }

    return x;
}
