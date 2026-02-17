struct Z{
    string s;
    int n;
    vector<int> z;

    // z[i] = max k s.t. s[i:i+k] == s[0:k]

    void init(string s_){
        s = s_;
        n = s.length();
        z.resize(n);

        int l = 0;
        int r = 0;
        z[0] = n;

        for (int i = 1; i < n; i++){
            if (i > r){
                l = r = i;
                while (r < n && s[r-l] == s[r]) r++;
                z[i] = r-l;
                r--;
            }else{
                int k = i - l;
                if (z[k] < r-i+1) z[i] = z[k];
                else{
                    l = i;
                    while (r < n && s[r-l] == s[r]) r++;
                    z[i] = r - l;
                    r--;
                }
            }
        }
    }

    int get(int k){
        return z[k];
    }
};
