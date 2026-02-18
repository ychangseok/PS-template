struct BinaryTrie{
    const int SZ = 32;
    struct Node{
        int sz[2], idx[2];

        Node(){
            for (int i = 0; i < 2; i++){
                sz[i] = 0;
                idx[i] = -1;
            }
        }
    };
    vector<Node> node;

    BinaryTrie(){
        node.push_back(Node());
    }

    void insert(ll n){
        int idx = 0;

        for (int j = 0; j < SZ; j++){
            int k = (n & (1LL << (SZ-j-1))) > 0;

            if (node[idx].idx[k] == -1){
                node.push_back(Node());
                node[idx].sz[k]++;
                node[idx].idx[k] = node.size()-1;
                idx = node.size()-1;
            }else{
                node[idx].sz[k]++;
                idx = node[idx].idx[k];
            }
        }
    }

    ll maxxor(ll n){
        ll res = 0;
        int idx = 0;
        for (int j = 0; j < SZ; j++){
            int k = (n & (1LL << (SZ-j-1))) > 0;

            if (node[idx].idx[1-k] == -1){
                idx = node[idx].idx[k];
            }else{
                res += (1LL << (SZ-j-1));
                idx = node[idx].idx[1-k];
            }
        }

        return res;
    }
};
