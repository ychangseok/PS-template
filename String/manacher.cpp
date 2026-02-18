vector<int> manacher(string s){
    string ss;
    for (char c : s){
        ss.push_back('#');
        ss.push_back(c);
    }
    ss.push_back('#');

    int r = -1;
    int c = -1;
    int ll = ss.length();

    vector<int> res(ll);

    for (int i = 0; i < ll; i++){
        if (i <= r){
            res[i] = min(r-i, res[c + (c-i)]);
        }

        while (i + res[i] + 1 < ll && i - res[i] - 1 >= 0 && ss[i + res[i] + 1] == ss[i - res[i] - 1]){
            res[i]++;
        }

        if (i + res[i] > r){
            c = i;
            r = i + res[i];
        }
    }

    return res;
}
