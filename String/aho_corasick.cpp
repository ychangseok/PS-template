struct Aho_corasick{
    struct Trie{
        struct Node{
            array<int, 26> nxt;
            int fail;
            bool output;

            Node() {
                nxt = {-1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                       -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                       -1, -1, -1, -1, -1, -1};
                output = false;
                fail = 0;
            }
        };

        vector<Node> node;

        Trie(){
            node.push_back(Node());
        }

        void insert(const string &s, int outputidx){
            int idx = 0;

            for (auto c : s){
                int k = c - 'a';

                if (node[idx].nxt[k] == -1){
                    node.push_back(Node());
                    node[idx].nxt[k] = node.size() - 1;
                    idx = node.size() - 1;
                }else{
                    idx = node[idx].nxt[k];
                }
            }

            node[idx].output = true;
        }
    };

    Trie trie;
    int strcnt;

    Aho_corasick(const vector<string>& v){
        trie = Trie();
        strcnt = 0;

        for (auto s : v){
            strcnt++;
            trie.insert(s, strcnt);
        }

        queue<int> q;
        q.push(0);
        trie.node[0].fail = 0;

        while (!q.empty()){
            int u = q.front();
            q.pop();

            auto curnode = trie.node[u];

            for (int i = 0; i < 26; i++){
                if (curnode.nxt[i] == -1) continue;

                if (u == 0) trie.node[curnode.nxt[i]].fail = 0;
                else {
                    int j = curnode.fail;
                    while (j && trie.node[j].nxt[i] == -1) j = trie.node[j].fail;
                    
                    if (trie.node[j].nxt[i] != -1) j = trie.node[j].nxt[i];
                    trie.node[curnode.nxt[i]].fail = j;
                }

                if (trie.node[trie.node[curnode.nxt[i]].fail].output)
                    trie.node[curnode.nxt[i]].output = true;
                
                q.push(curnode.nxt[i]);
            }
        }
    }

    bool matching(const string &s){
        int idx = 0;
        for (auto c : s){
            int k = c - 'a';

            while (idx > 0 && trie.node[idx].nxt[k] == -1)
                idx = trie.node[idx].fail;

            if (trie.node[idx].nxt[k] != -1)
                idx = trie.node[idx].nxt[k];
            
            if (trie.node[idx].output)
                return true;
        }

        return false;
    }
};
