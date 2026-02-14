int getplane(ll x, ll y){
    if (y == 0){
        if (x > 0) return 0;
        return 4;
    }
    if (x == 0){
        if (y > 0) return 2;
        return 6;
    }

    if (x > 0 && y > 0){
        return 1;
    }
    if (x < 0 && y > 0){
        return 3;
    }
    if (x > 0 && y < 0){
        return 7;
    }
    if (x < 0 && y < 0){
        return 5;
    }
}
ll ccw(POINT<ll> s1, POINT<ll> s2){
    return s1.x*s2.y - s1.y*s2.x;
}
bool cmp (POINT<ll> s1, POINT<ll> s2){
    int d1 = getplane(s1.x, s1.y);
    int d2 = getplane(s2.x, s2.y);

    if (d1 == d2){
        if (ccw(s1, s2) == 0){
            return s1.x*s1.x + s1.y*s1.y < s2.x*s2.x + s2.y*s2.y;
        }
        return ccw(s1, s2) > 0;
    }
    return d1 < d2;
}
