int isIntersect2(PT A, PT B, PT C, PT D){
    // check segment AB and segment CD intersects
    // parallel -> 2, intersect -> 1, other -> 0

	ll ab = ccw(A, B, C) * ccw(A, B, D);
	ll cd = ccw(C, D, A) * ccw(C, D, B);
    
    if (((B-A)^(D-C)) == 0) return 2;
    if (ab <= 0 && cd < 0) return 1;
    return 0;
}
bool intersect(const polygon &v, PT p1, PT p2){
    // check segment p1-p2 and interior of v intersects

    if (v.size() < 3) return false;

    for (int i = 0; i < v.size(); i++){
        int k = isIntersect2(p1, p2, v[i], v[(i+1)%v.size()]);
        if (k == 2) continue;
        if (k == 1) return true;
    }

    PT p = (p1 + p2);
    p.x /= 2;
    p.y /= 2;
    
    if (PointInConvexPolygon(v, p)) return true;
    return false;
}
