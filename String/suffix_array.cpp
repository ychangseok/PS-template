struct SA{
    int n, d;
    string s;
    vector<int> sa, pos, lcp, sainv;

    SA (string s_){
        s = s_;
        n = s.length();
        init();
    }

    bool cmp(int ii, int jj){
        if (pos[ii] != pos[jj]) return pos[ii] < pos[jj];

        ii += d;
        jj += d;
        return (ii < n && jj < n) ? (pos[ii] < pos[jj]) : (ii > jj);
    }
    void init(){
        sa.resize(n);
        lcp.resize(n);
        pos.resize(n);
        sainv.resize(n);

        for (int i = 0; i < n; i++){
            sa[i] = i;
            pos[i] = s[i];
        }

        for (d = 1; ; d *= 2){
            sort(all(sa), 
                [&](int ii, int jj) -> bool{
                    if (pos[ii] != pos[jj]) return pos[ii] < pos[jj];

                    int i2 = ii + d;
                    int j2 = jj + d;
                    return (i2 < n && j2 < n) ? (pos[i2] < pos[j2]) : (i2 > j2);
                }
            );

            vector<int> tmp(n);
            
            for (int i = 0; i < n-1; i++){
                tmp[i+1] = tmp[i] + cmp(sa[i], sa[i+1]);
            }

            for (int i = 0; i < n; i++){
                pos[sa[i]] = tmp[i];
            }

            if (tmp[n-1] == n-1) break;
        }

        for (int i = 0, k = 0; i < n; i++, k = max(k-1, 0)){
            if (pos[i] == n-1) continue;

            for (int j = sa[pos[i]+1]; max(i+k, j+k) < s.size() && s[i+k] == s[j+k]; k++);

            lcp[pos[i]] = k;
        }

        for (int i = 0; i < n; i++){
            sainv[sa[i]] = i;
        }
    }
};
