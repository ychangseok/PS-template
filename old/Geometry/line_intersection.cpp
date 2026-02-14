bool isIntersect(POINT<ll> A, POINT<ll> B, POINT<ll> C, POINT<ll> D){
    // check segment AB and segment CD intersects

	pll a = {A.x, A.y};
	pll b = {B.x, B.y};
	pll c = {C.x, C.y};
	pll d = {D.x, D.y};

	ll ab = ccw(a, b, c) * ccw(a, b, d);
	ll cd = ccw(c, d, a) * ccw(c, d, b);
	if (ab == 0 && cd == 0){
		if (a > b) swap(a, b);
		if (c > d) swap(c, d);
		return c <= b && a <= d;
	}
	return ab <= 0 && cd <= 0;
}

POINT<lb> getIntersectionPoint(POINT<ll> A, POINT<ll> B, POINT<ll> C, POINT<ll> D){
    ll x1, y1, x2, y2, x3, y3, x4, y4;

    x1 = A.getpos().first;
    y1 = A.getpos().second;
    x2 = B.getpos().first;
    y2 = B.getpos().second;
    x3 = C.getpos().first;
    y3 = C.getpos().second;
    x4 = D.getpos().first;
    y4 = D.getpos().second;

    if (x1 > x2){
        swap(x1, x2);
        swap(y1, y2);
    } else if (x1 == x2 && y1 > y2){
        swap(y1, y2);
    }

    if (x3 > x4){
        swap(x3, x4);
        swap(y3, y4);
    } else if (x3 == x4 && y3 > y4){
        swap(y3, y4);
    }

    if ((x4 - x3) * (y2 - y1) == (x2 - x1) * (y4 - y3)){
        // same slope

        if (x1 == x4 && y1 == y4){
            return POINT<lb>(x1, y1);
        }else if (x2 == x3 && y2 == y3){
            return POINT<lb>(x2, y2);
        }
    } else{
        // different slope and intersect
        // only one intersection point

        // x1 + s(x2-x1) == x3 + t(x4-x3)
        // y1 + s(y2-y1) = y3 + t(y4-y3)
        // solve for s, t

        if (x3 != x4){
            lb x = x1*(y3-y4) + x3*(y4-y1) + x4*(y1-y3);
            x /= (x1-x2)*(y3-y4) + x3*(y2-y1) + x4*(y1-y2);
            lb y = x1*(y3-y2) + x2*(y1-y3) + x3*(y2-y1);
            y /= (x1-x2)*(y3-y4) + x3*(y2-y1) + x4*(y1-y2);

            return POINT<lb>(x1 + (x2-x1)*x, y1 + (y2-y1)*x);
        }else{
            lb x = x1 - x4;
            x /= x1 - x2;
            lb y = x1*(y3-y2) + x2*(y1-y3) + x4*(y2-y1);
            y /= (x1-x2)*(y3-y4);

            return POINT<lb>(x1 + (x2-x1)*x, y1 + (y2-y1)*x);
        }
    }
}
