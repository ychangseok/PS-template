// 360 degree ccw angle sort centered on p
sort(all(pts),
    [&p](const PT &p1, const PT &p2) -> bool{
        if (p2 == p) return false;
        if (p1 == p) return true;
        if (p1 > p != p2 > p) return p1 < p2;
        return ccw(p, p1, p2) > 0;
    }
);
