bool PointInConvexPolygon(const polygon &v, const PT &p){
	// https://github.com/justiceHui/icpc-teamnote/blob/master/code/Geometry/PointInConvexPolygon.cpp
	// v : counterclockwise

	if (ccw(v[0], v[1], p) < 0) return false;

	int l = 1;
	int r = v.size() - 1;

	while (l < r){
		int m = (l + r + 1) / 2;
		if (ccw(v[0], v[m], p) >= 0){
			l = m;
		}else{
			r = m-1;
		}
	}

	if (l == v.size() - 1){
		return isIntersect(v[0], v.back(), p, p);
	}
	return ccw(v[0], v[l], p) >= 0 && ccw(v[l], v[l+1], p) >= 0 && ccw(v[l+1], v[0], p) >= 0;
}
