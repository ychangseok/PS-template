template <class T>
class segTree{
public:
    // segTree stores f([left, right])
    // needs to only change f_identity and f_merge() for different f

    segTree(vector<T> a_, int n_, T f_identity_, function<T(T, T)> func) : a(a_), n(n_), f_identity(f_identity_), f(func) {
        int maxn = getMax(n);
        tree.resize(maxn); 
        init(1, 0, n-1);
    }

    T Query(int left, int right){
        // returns f-value of segment [left, right]
        return query(1, 0, n-1, left, right);
    }

    void Update(int index, T val){
        // a[index] <- val
        update(1, 0, n-1, index, val);
    }

    void Update_diff(int index, T val){
        // a[index] += val
        Update(index, f_merge(Query(index, index), val));
    }

    T Getkth(int k){
        return getkth(1, 0, n-1, k);
    }

private:
    int n;
    T f_identity;
    vector<T> a;
    vector<T> tree;
    function<T(T, T)> f;

    int getMax(int n){
        return 4*n;
    }

    void init(int node, int start, int end){
        // initializing segment tree
        if (start == end) tree[node] = a[start];
        else{
            init(node*2, start, (start+end)/2);
            init(node*2+1, (start+end)/2+1, end);
            tree[node] = f_merge(tree[node*2], tree[node*2+1]);
        }
    }

    inline T f_merge(T lval, T rval){
        return f(lval, rval);
    }

    T query(int node, int start, int end, int left, int right){
        // node contains f-value of [start, end]
        // we want f-value of [left, right]

        if (left > end || right < start){
            return f_identity;
        }
        if (left <= start && end <= right){
            return tree[node];
        }

        T lsum = query(node*2, start, (start+end)/2, left, right);
        T rsum = query(node*2+1, (start+end)/2+1, end, left, right);
        return f_merge(lsum, rsum);
    }

    void update(int node, int start, int end, int index, T val){
        // node contains f-value of [start, end]
        // update a[index] <- val

        if (index < start || index > end){
            return;
        }

        if (start == end){
            tree[node] = val;
            return;
        }

        update(node*2, start, (start+end)/2, index, val);
        update(node*2+1, (start+end)/2+1, end, index, val);
        tree[node] = f_merge(tree[node*2], tree[node*2+1]);
    }

    T getkth(int node, int start, int end, int k){
        if (start == end) return start;

        if (tree[node*2] >= k){
            return getkth(node*2, start, (start+end)/2, k);
        }else{
            return getkth(node*2+1, (start+end)/2+1, end, k-tree[node*2]);
        }
    }

};
