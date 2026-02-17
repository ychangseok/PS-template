vector<int> kmp(string s, string t){
    // https://m.blog.naver.com/PostView.naver?blogId=kks227&logNo=220917078260&proxyReferer=https:%2F%2Fwww.google.com%2F&trackingCode=external
    
    int n = s.length();
    int m = t.length();

    vector<int> fail(m);

    // calculate failure function
    // fail[i] = max k s.t. t[0..k-1] = t[i-k+1..i]

    for (int i = 1, j = 0; i < m; i++){
        while (j > 0 && t[i] != t[j]) j = fail[j-1];
        if (t[i] == t[j]) {
            j++;
            fail[i] = j;
        }
    }

    // string matching
    vector<int> res;

    for (int i = 0, j = 0; i < n; i++){

        while (j > 0 && s[i] != t[j]) j = fail[j-1];

        if (s[i] == t[j]){
            if (j == m - 1){
                // s[i:i+m] == t
                res.push_back(i - j + 1);
                j = fail[j];
            }else{
                j++;
            }
        }
    }

    return res;
}
