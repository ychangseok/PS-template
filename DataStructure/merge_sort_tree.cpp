template <class T>
class mergeSortTree{
public:
    mergeSortTree(vector<T> a_, int n_) : a(a_), n(n_) {
        int maxn = getMax(n);
        tree.resize(maxn); 
        init(1, 0, n-1);
    }

    ll Query(int left, int right, ll val, bool lower_bound = false){
        // if lower_bound = true,
        //   # of elt in [left, right] with elt <= val
        // else
        //   # of elt in [left, right] with elt>val
        return query(1, 0, n-1, left, right, val, lower_bound);
    }


private:
    int n;
    vector<T> a;
    vector<T> tree;

    int getMax(int n){
        return 4*n;
    }

    void init(int node, int start, int end){
        // initializing merge sort tree
        if (start == end) {
            tree[node] = a[start];
            return;
        }

        init(node*2, start, (start+end)/2);
        init(node*2+1, (start+end)/2+1, end);
        
        vector<ll> tmp;
        merge(all(tree[node*2]), all(tree[node*2+1]), back_inserter(tmp));
        tree[node] = tmp;
    }

    ll query(int node, int start, int end, int left, int right, ll val, bool lower_bound=false){
        if (left > end || right < start){
            return 0;
        }
        if (left <= start && end <= right){
            if (lower_bound){
                return upper_bound(all(tree[node]), val) - tree[node].begin();
            }else{
                return tree[node].end() - upper_bound(all(tree[node]), val);
            }
        }

        ll lsum = query(node*2, start, (start+end)/2, left, right, val, lower_bound);
        ll rsum = query(node*2+1, (start+end)/2+1, end, left, right, val, lower_bound);
        return lsum + rsum;
    }

};
