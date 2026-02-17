array<ll, 3> closestPoint(int n, polygon v){
    // returns square of distance of cloest points in v
    
    if (n == 2) return {(v[0]-v[1]).size(), v[0].idx, v[1].idx};
    if (n == 3) {
        vector<array<ll, 3>> tmp;
        for (int i = 0; i < 3; i++){
            for (int j = i+1; j < 3; j++){
                tmp.push_back({(v[i]-v[j]).size(), v[i].idx, v[j].idx});
            }
        }
        sort(all(tmp));
        return tmp[0];
    }

    sort(all(v), 
        [](PT p1, PT p2)->bool{
            return p1.x < p2.x;
        }
    );
    ll x_mid = v[n/2].x;

    polygon v_left = polygon(v.begin(), v.begin() + n/2);
    polygon v_right = polygon(v.begin() + n/2, v.end());

    auto d1 = closestPoint(n/2, v_left);
    auto d2 = closestPoint(n-n/2, v_right);
    auto d = d1;
    if (d1[0] > d2[0]) d = d2;

    polygon w;
    for (int i = 0; i < n; i++){
        if (pow(v[i].x - x_mid, 2) <= d[0]){
            w.push_back(v[i]);
        }
    }

    sort(all(w), 
        [](PT p1, PT p2)->bool{
            return p1.y < p2.y;
        }
    );

    int m = w.size();

    for (int i = 0; i < m; i++){
        int j = i + 1;
        while (j < m && pow(w[j].y - w[i].y, 2) <= d[0]){
            if ((w[i]-w[j]).size() < d[0]){
                d[0] = (w[i]-w[j]).size();
                d[1] = w[i].idx;
                d[2] = w[j].idx;
            }
            j++;
        }
    }

    return d;
}
