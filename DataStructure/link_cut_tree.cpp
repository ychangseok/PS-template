template <class T>
struct LinkCutTree{
public:
    LinkCutTree(int n){
        ptr.resize(n+1);
        for (int i = 1; i <= n; i++) ptr[i] = new Node(i);
    }

    int lca(int u, int v){
        return lca(ptr[u], ptr[v])->num;
    }

    void update(int u, T val){
        update(ptr[u], val);
    }

    void cut(int u, int v=0){
        if (v){
            if (lca(u, v) == u) cut(ptr[v]);
            else cut(ptr[u]);
        }else{
            cut(ptr[u]);
        }
    }

    void connect(int u, int v){
        connect(ptr[u], ptr[v]);
    }

    T query(int u, int v){
        return query(ptr[u], ptr[v]);
    }
private:
    const T T_id = 0;
    struct Node{
        Node *l, *r, *p, *pp;
        bool flip;

        T v, q;
        int num; // node number

        Node(int i=0){
            num = i;
            l = r = p = pp = nullptr;
            flip = false;
            v = q = T_id;
        }
    };

    vector<Node*> ptr;

    inline T merge(T v1, T v2){
        return v1+v2;
    }

    void init(Node* u){
        u->q = u->v;
        if (u->l) u->q = merge(u->q, u->l->q);
        if (u->r) u->q = merge(u->q, u->r->q);
    }

    void update(Node* u, T val){
        access(u);
        u->v = val;
        init(u);
    }

    void push(Node *cur){
        if (!cur->flip) return;
        swap(cur->l, cur->r);
        cur->flip = false;
        if (cur->l) cur->l->flip = !cur->l->flip;
        if (cur->r) cur->r->flip = !cur->r->flip;
    }

    void rotate(Node *x){
        Node *p = x->p;
        if (!p) exit(2);

        push(p);
        push(x);

        if (x == p->l){
            if ((p->l = x->r)) x->r->p = p; 
            x->r = p;
        }else{
            if ((p->r = x->l)) x->l->p = p;
            x->l = p;
        }

        x->p = p->p;
        p->p = x;

        if (x->p){
            if (p == x->p->l) x->p->l = x;
            else x->p->r = x;
        }else{
            x->pp = p->pp;
            p->pp = nullptr;
        }

        init(p);
        init(x);
    }

    void splay(Node* x){
        while (x->p){
            Node *p = x->p;
            Node *g = p->p;

            if (g) {
                if ((x==p->l) == (p==g->l)) rotate(p);
                else rotate(x);
            }
            rotate(x);
        }
    }

    void access(Node *u){
        splay(u);
        push(u);

        if (u->r){
            u->r->pp = u;
            u->r->p = nullptr;
            u->r = nullptr;
        }

        while (u->pp){
            Node *pp = u->pp;

            splay(pp);
            push(pp);
            if (pp->r){
                pp->r->pp = pp;
                pp->r->p = nullptr;
            }

            pp->r = u;
            u->p = pp;
            u->pp = nullptr;

            splay(u);
        }
    }

    Node* find_root(Node* u){
        access(u);
        while (u->l) {
            u = u->l;
            push(u);
        }
        access(u);
        return u;
    }
    
    void cut(Node *u){
        access(u);
        if (u->l){
            u->l->p = nullptr;
            u->l = nullptr;
            init(u);
        }
    }

    void link(Node *u, Node *v){
        // par[u] = v로 간선 추가
        access(u);
        access(v);
        u->l = v;
        v->p = u;
        init(u);
    }
    void make_root(Node* u){
        access(u);
        u->flip = !u->flip;
    }
    void connect(Node* u, Node* v){
        // assume u and v are in the different represented tree
        make_root(u);
        link(u, v);
    }

    Node* lca(Node* u, Node* v){
        // assume u and v are in the same represented tree
        access(u);
        access(v);
        splay(u);
        if (u->pp) return u->pp;
        return u;
    }

    T pathquery(Node* l, Node* u, bool includeroot=true){
        if (l->num == u->num) {
            if (includeroot) return l->v;
            else return T_id;
        }
        access(l);
        access(u);
        splay(l);
        l->r->p = nullptr;
        splay(u);
        u->p = l;

        T res = u->v;
        if (includeroot) res = merge(res, l->v);
        if (l->r->l) res = merge(res, l->r->l->q);
        return res;        
    }
    T query(Node* u, Node* v){
        Node* l = lca(u, v);
        return merge(pathquery(l, u), pathquery(l, v, false));
    }
};
