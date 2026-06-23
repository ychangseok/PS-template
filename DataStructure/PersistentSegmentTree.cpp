template <class T>
struct PersistentSegmentTree{
public:
    PersistentSegmentTree(int n_){
        n = n_;
        tree.resize(MAX_NODE);
    }

    int build(const vector<ll> &arr){
        return build(0, n-1, arr);
    }

    T query(int root, int left, int right){
        return query(root, 0, n-1, left, right);
    }

    int update(int root, int idx, T val){
        return update(root, 0, n-1, idx, val);
    }

    int add_copy(int root){
        tree[sz] = tree[root];
        return sz++;
    }
private:
    struct Node{
        int l, r;
        T val;

        Node(ll a=0){
            val = T(a);
            l = r = 0;
        }
        Node(T val_, int l_, int r_){
            val = val_;
            l = l_;
            r = r_;
        }
    };

    // must be larger than 2n + q(logn + 2)
    const int MAX_NODE = 4322000;
    T T_id = 0; // change

    int n;
    int sz = 1;
    vector<Node> tree;

    inline T merge(T n1, T n2){
        return n1 + n2;
    }

    Node join(int l, int r){
        return Node(merge(tree[l].val, tree[r].val), l, r);
    }

    int build(int start, int end, const vector<ll> &v){
        if (start == end){
            tree[sz] = Node(v[start]);
            return sz++;
        }

        int mid = (start + end) / 2;
        tree[sz] = join(build(start, mid, v), build(mid+1, end, v));
        return sz++;
    }

    int update(int node, int start, int end, int idx, T val){
        if (start == end){
            tree[sz] = Node(val);
            return sz++;
        }

        int mid = (start + end) / 2;
        if (idx <= mid) tree[sz] = join(update(tree[node].l, start, mid, idx, val), tree[node].r);
        else tree[sz] = join(tree[node].l, update(tree[node].r, mid+1, end, idx, val));

        return sz++;
    }

    T query(int node, int start, int end, int left, int right){
        if (right < start || left > end) return T_id;
        if (left <= start && end <= right) return tree[node].val;

        int mid = (start + end) / 2;

        T lval = query(tree[node].l, start, mid, left, right);
        T rval = query(tree[node].r, mid+1, end, left, right);
        return merge(lval, rval);
    }
};
