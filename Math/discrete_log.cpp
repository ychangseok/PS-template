ll discrete_log(ll p, ll g, ll h){
	// baby step giant step
	// O(sqrt{p} log p)
	
	// find x in [0, P) such that
	// g^x == h (mod p)
	// g is primitive root of  p
	// p is prime
	
	map<ll, ll> m;
	
	ll b = ll(sqrt(p-1)) + 1;
		
	for (ll v = 0; v < b; v++){
		ll tmp = power(g, p-2, p);
		m.insert({mul(h, power(tmp, v, p), p), v});
	}
		
	ll ans = p;
	g = power(g, b, p);
	for (ll u = 0; u < b; u++){
		ll tmp = power(g, u, p);
		if (m.find(tmp) != m.end()){
			ans = u*b + m[tmp];
			break;
		}
	}
	
	return ans;
}
