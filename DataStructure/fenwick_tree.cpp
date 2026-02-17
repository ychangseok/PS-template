struct Fenwick{
    // range sum, point update

    int n;
    vector<int> tree;

    Fenwick(int n_){
        n = n_;
        while (n != (n & -n)){
            n += n & -n;
        }
        tree = vector<int>(n+1);
    }
    
    ll sum(int i){
        ll res = 0;
        while (i > 0){
            res += tree[i];
            i -= (i & -i);
        }
        return res;
    }
    ll query(int l, int r){
        return sum(r) - sum(l-1);
    }
    void add(int i, ll val){
        while (i <= n){
            tree[i] += val;
            i += (i & -i);
        }
    }
};
