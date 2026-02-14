template <class T>
CIRCLE<lb> minimum_enclosing_circle(vector<POINT<T> > v){
    // returns minimum_enclosing_circle that contains every POINT in v
    // O(n^3) 

    priority_queue<CIRCLE<lb> > pq;
    int n = v.size();

    for (int i = 0; i < n; i++){
        for (int j = i+1; j < n; j++){
            for (int k = j+1; k < n; k++){
                CIRCLE<lb> c = enclosing_circle<ll>(v[i], v[j], v[k]);

                bool check = true;

                for (int l = 0; l < n; l++){
                    if (v[l].to_lb().dist(c.center()) > c.r){
                        check = false;
                    }
                }

                if (check){
                    pq.push(c);
                }
            }
        }
    }

    for (int i = 0; i < n; i++){
        for (int j = i+1; j < n; j++){
            CIRCLE<lb> c((v[i].x + v[j].x)/2, (v[i].y+v[j].y)/2, v[i].dist(v[j])/2);

            bool check = true;

            for (int l = 0; l < n; l++){
                if (v[l].to_lb().dist(c.center()) > c.r){
                    check = false;
                }
            }

            if (check){
                pq.push(c);
            }
        }
    }

    return pq.top();
}
