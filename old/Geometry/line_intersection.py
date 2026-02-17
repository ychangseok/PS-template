def ccw(p1, p2, p3):
    op = p1[0]*p2[1] + p2[0]*p3[1] + p3[0]*p1[1]
    op -= p1[1]*p2[0] + p2[1]*p3[0] + p3[1]*p1[0]
    return (op > 0) - (op < 0)
def comp(p1, p2):
    return p1[0] > p2[0] or (p1[0] == p2[0] and p1[1] > p2[1])
def isIntersect(p1, p2, p3, p4):
    ab = ccw(p1, p2, p3) * ccw(p1, p2, p4)
    cd = ccw(p3, p4, p1) * ccw(p3, p4, p2)

    if ab == 0 and cd == 0:
        if comp(p1, p2):
            p1, p2 = p2, p1
        if comp(p3, p4):
            p3, p4 = p4, p3

        return not comp(p3, p2) and not comp(p1, p4)

    return ab <= 0 and cd <= 0
def getIntersect(p1, p2, p3, p4):
    # [p1, p2] and [p3, p4] intersect

    if comp(p1, p2):
        p1, p2 = p2, p1
    if comp(p3, p4):
        p3, p4 = p4, p3
    
    if (p4[0]-p3[0])*(p2[1]-p1[1]) == (p2[0]-p1[0])*(p4[1]-p3[1]):
        if p1 == p4:
            return p1
        elif p2 == p3:
            return p2
    else:
        if p3[0] != p4[0]:
            x = F(p1[0]*(p3[1]-p4[1]) + p3[0]*(p4[1]-p1[1]) + p4[0]*(p1[1]-p3[1]),
                  (p1[0]-p2[0])*(p3[1]-p4[1]) + p3[0]*(p2[1]-p1[1]) + p4[0]*(p1[1]-p2[1]))
            
            return [p1[0] + (p2[0]-p1[0])*x, p1[1] + (p2[1]-p1[1])*x]
        else:
            x = F(p1[0]-p4[0], p1[0]-p2[0])
            return [p1[0] + (p2[0]-p1[0])*x, p1[1] + (p2[1]-p1[1])*x]
