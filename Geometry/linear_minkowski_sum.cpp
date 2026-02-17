void reorder(polygon &P){
    int pos = 0;
    int n = P.size();

    for (int i = 1; i < n; i++){
        if (P[i].y < P[pos].y || (P[i].y == P[pos].y && P[i].x < P[pos].x)){
            pos = i;
        }
    }

    rotate(P.begin(), P.begin()+pos, P.end());
}
polygon minkowski_sum (polygon P, polygon Q){
    // minkowski sum of two convex polygon
    // O(|P| + |Q|)
    
    reorder(P);
    reorder(Q);

    int psz = P.size();
    int qsz = Q.size();

    polygon res;
    int i = 0;
    int j = 0;

    while (i < psz || j < qsz){
        res.push_back(P[i%psz]+Q[j%qsz]);

        ll crs = (P[(i+1)%psz]-P[i%psz])^(Q[(j+1)%qsz]-Q[j%qsz]);
        
        if (crs >= 0 && i < psz) i++;
        if (crs <= 0 && j < qsz) j++;
    }

    return res;
}
