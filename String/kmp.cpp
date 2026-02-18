vector<int> kmp(string s, string t){
    int n = s.length();
    int m = t.length();

    vector<int> fail(m);

    // fail[i] = max k s.t. t[0..k-1] = t[i-k+1..i]

    for (int i = 1, j = 0; i < m; i++){
        while (j > 0 && t[i] != t[j]) j = fail[j-1];
        if (t[i] == t[j]) {
            j++;
            fail[i] = j;
        }
    }

    vector<int> res;
    for (int i = 0, j = 0; i < n; i++){
        while (j > 0 && s[i] != t[j]) j = fail[j-1];

        if (s[i] == t[j]){
            if (j == m - 1){
                res.push_back(i - j + 1);
                j = fail[j];
            }else{
                j++;
            }
        }
    }

    return res;
}
