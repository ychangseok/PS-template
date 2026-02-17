struct Line{
    PT p, d, p2;

    Line(PT a, PT b){
        p = a;
        p2 = b;
        d = b - a;
    }
};
bool line_intersect(const PT &s1, const PT &e1, const PT &s2, const PT &e2, PT &v){
    PT v1 = e1 - s1;
    PT v2 = e2 - s2;
    lb det = v1 ^ v2;
    if (det == 0) return false;
    lb s = ((s2-s1)^v2) / (v1 ^ v2);
    v = s1 + v1 * s;
    return true;
}
polygon HPI(vector<Line>& lines){
    auto bad = [](const Line &a, const Line &b, const Line &c){
        PT v;
        if (!line_intersect(a.p, a.p2, b.p, b.p2, v)) return false;
        lb cross = c.d^(v-c.p);
        return cross <= 0;
    };

    sort(all(lines),
        [](const Line &l1, const Line &l2) -> bool{
            if (l1.d < O != l2.d < O) return l1.d < l2.d;
            return (l1.d^l2.d) > 0;
        }
    );

    deque<Line> dq;

    for (auto line : lines){
        while (dq.size() >= 2 && bad(dq[dq.size()-2], dq.back(), line))
            dq.pop_back();

        while (dq.size() >= 2 && bad(dq[0], dq[1], line))
            dq.pop_front();
        
        if (dq.empty()) dq.push_back(line);
        else if ((dq.back().d ^ line.d) == 0){
            if ((dq.back().d * line.d) < 0){
                // inter is zero
                return polygon();
            }else if (((line.p-dq.back().p)^dq.back().d) < 0){
                dq.pop_back();
                dq.push_back(line);
            }
        }else if (dq.size() < 2 || !bad(dq.back(), line, dq[0]))
            dq.push_back(line);
    }

    polygon res;
    if (dq.size() >= 3){
        for (int i = 0; i < dq.size(); i++){
            int j = (i+1)%dq.size();
            PT v;
            if (!line_intersect(dq[i].p, dq[i].p2, dq[j].p, dq[j].p2, v)) continue;
            res.push_back(v);
        }
    }
    return res;
}
