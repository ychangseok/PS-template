template <class T, class S>
struct SplayTree{
public:

    T query(int s, int e){
        return gather(s, e)->sum;
    }

    void set(int s, ll val){
        kth(s);
        tree->v = val;
        update(tree);
    }
    
    void range_update(int s, int e, S val){
        Node* x = gather(s, e);
        x->lazy = merge_lazy(x->lazy, val);
        x->sum += x->sz * val;
    }
    
    int getidx(int x){
        Node* x = ptr[p[x]];
        splay(x);
        return tree->l->sz;
    }

    void flip(int s, int e){
        Node* x = gather(s, e);
        x->flip = !x->flip;
    }
    
    void shift(int s, int e, int x){
        // [s, e]를 오른쪽으로 x만큼 shift
        int l = e - s + 1;
        if (x < 0) x = l + x;
        if (x >= l) x %= l;
        if (x == 0) return;

        flip(s, e-x);
        flip(e-x+1, e);
        flip(s, e);
    }

    SplayTree(ll a[], int n){
        if (tree) delete tree;

        ptr = vector<Node*>(n+2, nullptr);
        p = vector<int>(n+1, 0);

        tree = ptr[0] = new Node(-1);
        for (int i = 1; i <= n; i++){
            p[a[i]] = i;
            tree->r = ptr[i] = new Node(a[i], tree);
            tree = tree->r;
        }
        tree->r = ptr[n+1] = new Node(0, tree);

        for (int i = n+1; i >= 0; i--){
            update(ptr[i]);
        }
        
        splay(ptr[n/2]);
    }

    ~SplayTree() {
        if (tree) delete tree;
    }
private:
    struct Node{
        Node* l;
        Node* r;
        Node* p;
        int sz;
        bool flip;
        ll v;
        T sum;
        S lazy;


        Node(ll v_=0, Node* p_=nullptr){
            l = r = nullptr;
            p = p_;
            sz = 1;
            v = v_;
            sum = T(v_);
            lazy = S();
            flip = false;
        }

        ~Node() {
            if (l) delete l;
            if (r) delete r;
        }
    };

    Node* tree = nullptr;
    vector<Node*> ptr;
    vector<int> p;

    inline T merge_node(T n1, T n2){
        return n1+n2;
    }
    inline S merge_lazy(S n1, S n2){
        return n1+n2;
    }
    inline S act(T node, int l, int r, S lazy){

    }

    void push(Node* x){
        x->v += x->lazy;
        if (x->l){
            x->l->lazy = merge_lazy(x->l->lazy, x->lazy);
            x->l->sum += x->l->sz * x->lazy;
        }
        if (x->r){
            x->r->lazy = merge_lazy(x->r->lazy, x->lazy);
            x->r->sum += x->r->sz * x->lazy;
        }
        x->lazy = 0;
    }   
    void push(Node* x){
        if (x->flip){
            swap(x->l, x->r);
            if (x->l) x->l->flip = !x->l->flip;
            if (x->r) x->r->flip = !x->r->flip;
            x->flip = false;
        }
    }
    void update(Node *x){
        x->sz = 1;
        x->sum = T(x->v);
        if (x->l) {
            x->sz += x->l->sz;
            x->sum = merge_node(x->l->sum, x->sum);
        }
        if (x->r) {
            x->sz += x->r->sz;
            x->sum = merge_node(x->sum, x->r->sum);
        }
    }

    void rotate(Node *x){
        Node *p = x->p;
        Node *b = NULL;
        
        if (!p) return;
        
        push(p);
        push(x);

        if (x == p->l){
            p->l = b = x->r;
            x->r = p;
        }else{
            p->r = b = x->l;
            x->l = p;
        }

        x->p = p->p;
        p->p = x;
        if (b) b->p = p;

        if (x->p){
            if (p == x->p->l) x->p->l = x;
            else x->p->r = x;
        }else{
            tree = x;
        }

        update(p);
        update(x);
    }

    void splay(Node* x, Node* g = nullptr){
        while (x->p != g){
            Node *p = x->p;

            if (p->p == g) rotate(x);
            else {
                Node *pp = p->p;
                if ((x==p->l) == (p==pp->l)) rotate(p);
                else rotate(x);
                rotate(x);
            }
        }

        if (!g) tree = x;
    }

    void kth(int k){
        // 0 based
        Node* x = tree;
        push(x);
        while (1){
            while (x->l && x->l->sz > k) {
                x = x->l;
                push(x);
            }
            if (x->l) k -= x->l->sz;
            if (k == 0) break;
            k -= 1;
            x = x->r;
            push(x);
        }
        splay(x);
    }
    
    Node* gather(int s, int e){
        // gather [s, e]
        kth(e+1);
        Node* tmp = tree;
        kth(s-1);
        splay(tmp, tree);
        return tree->r->l;
    }
};
