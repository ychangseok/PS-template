//  Graham scan
vector<POINT> convex_hull(vector<POINT> v){
    int n = v.size();
    sort(all(v), cmp);

    for (int i = 1; i < n; i++){
        v[i].p = v[i].x - v[0].x;
        v[i].q = v[i].y - v[0].y;
    }

    sort(v.begin()+1, v.end(), cmp);
    
    vector<POINT> cvh;
    stack<int> st;
    int next = 2;

    st.push(0);
    st.push(1);

    while (next < n){
        while (st.size() >= 2){
            int second = st.top(); st.pop();
            int first = st.top();

            if (ccw(v[first], v[second], v[next]) > 0){
                st.push(second);
                break;
            }
        }
        st.push(next);
        next++;
    }

    while (!st.empty()){
        cvh.push_back(v[st.top()]);
        st.pop();
    }

    reverse(all(cvh));

    return cvh;
}
//  Monotone chain
vector<POINT<ll> > convex_hull(vector<POINT<ll> > v){
    // monotone chain

    int n = v.size();
    int k = 0;

    if (n < 3) return v;

    vector<POINT<ll> > ans(2*n);

    sort(all(v),
        [](POINT<ll> p1, POINT<ll> p2) -> bool{
            if (p1.x == p2.x) return p1.y < p2.y;
            return p1.x < p2.x;
        }
    );
    
    for (int i = 0; i < n; i++){
        while (k >= 2 && ccw(ans[k-2], ans[k-1], v[i]) < 0){
            k--;
        }
        ans[k] = v[i];
        k++;
    }

    for (int i = n- 1, t = k + 1; i > 0; i--){
        while (k >= t && ccw(ans[k-2], ans[k-1], v[i-1]) < 0){
            k--;
        }
        ans[k] = v[i-1];
        k++;
    }

    ans.resize(k-1);
    return ans;
}

bool bcw(const POINT<ll> &p1, const POINT<ll> &p2, const POINT<ll> &p3, bool include_collinear=false){
    ll op = p1.x*p2.y + p2.x*p3.y + p3.x*p1.y;
    op -= p1.y*p2.x + p2.y*p3.x + p3.y*p1.x;
    return (op < 0) || (op == 0 && include_collinear);
}
bool bccw(const POINT<ll> &p1, const POINT<ll> &p2, const POINT<ll> &p3, bool include_collinear=false){
    ll op = p1.x*p2.y + p2.x*p3.y + p3.x*p1.y;
    op -= p1.y*p2.x + p2.y*p3.x + p3.y*p1.x;
    return (op > 0) || (op == 0 && include_collinear);
}
bool bcw(pll a, pll b, pll c, bool include_collinear=false){
	POINT<ll> A(a.first, a.second);
	POINT<ll> B(b.first, b.second);
	POINT<ll> C(c.first, c.second);

	return bcw(A, B, C, include_collinear);
}
bool bccw(pll a, pll b, pll c, bool include_collinear=false){
	POINT<ll> A(a.first, a.second);
	POINT<ll> B(b.first, b.second);
	POINT<ll> C(c.first, c.second);

	return bccw(A, B, C, include_collinear);
}
// included option for collinear pts
void convex_hull(vector<POINT<ll> >&  v, bool include_collinear=false){
    // monotone chain

    if (v.size() == 1)
        return;
    
    sort(all(v),
        [](POINT<ll> p1, POINT<ll> p2) -> bool{
            if (p1.x == p2.x) return p1.y < p2.y;
            return p1.x < p2.x;
        }
    );

    int n = v.size();
    POINT<ll> p1 = v[0], p2 = v.back();

    vector<POINT<ll> > up, down;
    up.push_back(p1);
    down.push_back(p1);

    for (int i = 1; i < n; i++){
        if (i == n-1 || bcw(p1, v[i], p2, include_collinear)){
            while (up.size() >= 2 && !bcw(up[up.size()-2], up[up.size()-1], v[i], include_collinear)){
                up.pop_back();
            } 
            up.push_back(v[i]);
        }
        if (i == n-1 || bccw(p1, v[i], p2, include_collinear)){
            while (down.size() >= 2 && !bccw(down[down.size()-2], down[down.size()-1], v[i], include_collinear)){
                down.pop_back();
            }
            down.push_back(v[i]);
        }
    }

    if (include_collinear && up.size() == v.size()){
        // reverse(all(v));
        return;
    }
    v.clear();

    v.insert(v.end(), all(down));
    up.pop_back();
    reverse(all(up));
    up.pop_back();
    v.insert(v.end(), all(up));
}
