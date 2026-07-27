array<FPS, 2> sum_of_rational(const vector<FPS> &F, const vector<FPS> &G){
    // \sum F[i] / G[i] in O(n log^2n)
    assert (F.size() == G.size());
    int n = F.size();

    if (n == 0) return {FPS(1), FPS(1)};
    if (n == 1) return {F[0], G[0]};

    int mid = n / 2;
    vector<FPS> F1(F.begin(), F.begin()+mid);
    vector<FPS> F2(F.begin()+mid, F.end());
    vector<FPS> G1(G.begin(), G.begin()+mid);
    vector<FPS> G2(G.begin()+mid, G.end());

    auto [A, B] = sum_of_rational(F1, G1);
    auto [C, D] = sum_of_rational(F2, G2);
    return {A*D+B*C, B*D};
}
