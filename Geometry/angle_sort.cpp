// 360 degree ccw angle sort centered on p
sort(all(pts),
    [&C](const PT &p1, const PT &p2) -> bool{
        if (p2 == C) return false;
        if (p1 == C) return true;
        if (p1 > C != p2 > C) return p1 < p2;
        return ccw(C, p1, p2) > 0;
    }
);
