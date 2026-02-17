polygon convex_hull(polygon v){
    // monotone chain

    int n = v.size();
    int k = 0;

    if (n < 3) return v;

    polygon ans(2*n);

    sort(all(v));
    
    for (int i = 0; i < n; i++){
        while (k >= 2 && ccw(ans[k-2], ans[k-1], v[i]) <= 0){
            k--;
        }
        ans[k] = v[i];
        k++;
    }

    for (int i = n- 1, t = k + 1; i > 0; i--){
        while (k >= t && ccw(ans[k-2], ans[k-1], v[i-1]) <= 0){
            k--;
        }
        ans[k] = v[i-1];
        k++;
    }

    ans.resize(k-1);
    return ans;
}
