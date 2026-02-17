def bfs(s, t):
    parent = [-1 for _ in range(n)]
    parent[s] = -2

    Q = deque()
    Q.append([s, pow(3, 2001)])

    while Q:
        cur, flow = Q.popleft()
        # print(cur, flow)

        for nxt in graph[cur]:
            if parent[nxt] == -1 and capacity[cur][nxt]:
                parent[nxt] = cur
                new_flow = min(flow, capacity[cur][nxt])

                if nxt == t:
                    return [new_flow, parent]
                
                Q.append([nxt, new_flow])
    return [0, []]  
def maxflow(s, t):
    flow = 0
    
    while True:
        new_flow, parent = bfs(s, t)
        if new_flow == 0:
            break

        flow += new_flow
        cur = t

        # print(parent)

        while cur != s:
            prev = parent[cur]
            capacity[prev][cur] -= new_flow
            capacity[cur][prev] += new_flow
            cur = prev
    
    return flow
