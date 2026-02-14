int d, n;
vector<int> sa;
vector<int> lcp;
vector<int> pos;
bool cmp(int ii, int jj){
    if (pos[ii] != pos[jj]) return pos[ii] < pos[jj];

    ii += d;
    jj += d;
    return (ii < n && jj < n) ? (pos[ii] < pos[jj]) : (ii > jj);
}
void suffix_array(const string &s){
    // O(n log^2 n)

    n = s.length();
    sa.resize(n);
    lcp.resize(n);
    pos.resize(n);

    for (int i = 0; i < n; i++){
        sa[i] = i;
        pos[i] = s[i];
    }

    for (d = 1; ; d *= 2){
        sort(all(sa), cmp);

        vector<int> tmp(n);
        
        for (int i = 0; i < n-1; i++){
            tmp[i+1] = tmp[i] + cmp(sa[i], sa[i+1]);
        }

        for (int i = 0; i < n; i++){
            pos[sa[i]] = tmp[i];
        }

        if (tmp[n-1] == n-1) break;
    }

    // for (int i = 0; i < n; i++){
    //     cout << pos[sa[i]] << ' ';
    // }
    // cout << '\n';

    for (int i = 0, k = 0; i < n; i++, k = max(k-1, 0)){
        if (pos[i] == n-1) continue;

        for (int j = sa[pos[i]+1]; s[i+k] == s[j+k]; k++);

        lcp[pos[i]] = k;
    }

}
