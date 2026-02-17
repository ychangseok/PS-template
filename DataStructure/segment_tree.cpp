template <class T>
struct segTree{
    // 0-BASED
    vector<T> t;
    T id;
    int n;

    segTree(int n_, T id_){
        n = n_;
        id = id_;
        t = vector<T>(n*2, id);
    }

    inline T merge(T n1, T n2){

    }
    inline T add(T n1, T n2){
        
    }

    void update(int idx, T val){
        for (t[idx+=n] = val; idx >>= 1; ){
            t[idx] = merge(t[idx<<1], t[idx<<1|1]);
        }
    }
    void update_diff(int idx, T val){
        idx += n;
        t[idx] = add(t[idx], val);
        for (; idx >>= 1; ){
            t[idx] = merge(t[idx<<1], t[idx<<1|1]);
        }
    }

    T query(int l, int r){
        // [l, r)        
        T resl = id;
        T resr = id;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1){
            if (l&1) resl = merge(resl, t[l++]);
            if (r&1) resr = merge(t[--r], resr); 
        }
        return merge(resl, resr);
    }

};
