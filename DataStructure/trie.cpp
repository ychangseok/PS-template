struct Trie{
    vector<map<string, int> > node;

    Trie(){
        node.push_back(map<string, int>{});
    }

    void insert(const vector<string>& v){
        int idx = 0;
        for (string s : v){
            if (node[idx].find(s) == node[idx].end()){
                node.push_back(map<string, int>());
                node[idx].insert({s, node.size()-1});
                idx = node.size()-1;
            }else{
                idx = node[idx][s];
            }
        }   
    }

    void print(int idx=0, int lvl=0){
        for (auto s : node[idx]){
            for (int i = 0; i < lvl; i++){
                cout << "--";
            }
            cout << s.first << '\n';
            print(s.second, lvl+1);
        }
    }
};
