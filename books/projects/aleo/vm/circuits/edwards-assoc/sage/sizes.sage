import time
R.<a,d,x1,y1,x2,y2,x3,y3> = PolynomialRing(QQ, order='degrevlex')
C = [a*xi^2+yi^2-1-d*xi^2*yi^2 for (xi,yi) in [(x1,y1),(x2,y2),(x3,y3)]]
I = R.ideal(C)
e12 = d*x1*x2*y1*y2; nx12 = x1*y2+y1*x2; ny12 = y1*y2-a*x1*x2; D1=1+e12; D2=1-e12
e23 = d*x2*x3*y2*y3; nx23 = x2*y3+y2*x3; ny23 = y2*y3-a*x2*x3; D4=1+e23; D5=1-e23
NLx = nx12*y3*D2 + ny12*x3*D1; DLx = D1*D2 + d*x3*y3*nx12*ny12
NLy = ny12*y3*D1 - a*nx12*x3*D2; DLy = D1*D2 - d*x3*y3*nx12*ny12
NRx = x1*ny23*D4 + y1*nx23*D5; DRx = D4*D5 + d*x1*y1*nx23*ny23
NRy = y1*ny23*D4 - a*x1*nx23*D5; DRy = D4*D5 - d*x1*y1*nx23*ny23
for name,(NL,DL,NR,DR) in [('x',(NLx,DLx,NRx,DRx)),('y',(NLy,DLy,NRy,DRy))]:
    diff = NL*DR - NR*DL
    print(name, 'diff terms', len(diff.monomials()), 'deg', diff.degree())
    t=time.time()
    G = I.groebner_basis()
    r = diff.reduce(G)
    print(' reduced', r, time.time()-t)
    t=time.time()
    cof = diff.lift(I)
    print(' lift time', time.time()-t)
    for c in cof: print('  cof terms', len(c.monomials()), 'deg', c.degree(), 'denoms', lcm([q.denominator() for q in c.coefficients()]) if c!=0 else 1, 'maxcoef', max([abs(q) for q in c.coefficients()]) if c!=0 else 0)
    print(' check', diff - sum(c*g for c,g in zip(cof,C)) == 0)
