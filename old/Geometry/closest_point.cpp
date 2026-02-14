ll closestPoint(int n, vector<POINT<ll> > v){
    // returns square of distance of cloest points in v
    
    if (n == 2) return v[0].dist_square(v[1]);
    if (n == 3) return min(v[0].dist_square(v[1]), min(v[2].dist_square(v[0]), v[2].dist_square(v[1])));

    sort(all(v), cmp_x);
    ll x_mid = v[n/2].x;

    vector<POINT<ll> > v_left = vector<POINT<ll> >(v.begin(), v.begin() + n/2);
    vector<POINT<ll> > v_right = vector<POINT<ll> >(v.begin() + n/2, v.end());

    ll d1 = closestPoint(n/2, v_left);
    ll d2 = closestPoint(n-n/2, v_right);
    ll d = min(d1, d2);

    vector<POINT<ll> > w;
    for (int i = 0; i < n; i++){
        if (pow(v[i].x - x_mid, 2) <= d){
            w.push_back(v[i]);
        }
    }

    sort(all(w), cmp_y);
    int m = w.size();

    for (int i = 0; i < m; i++){
        int j = i + 1;
        while (j < m && pow(w[j].y - w[i].y, 2) <= d){
            d = min(d, w[i].dist_square(w[j]));
            j++;
        }
    }

    return d;
}
