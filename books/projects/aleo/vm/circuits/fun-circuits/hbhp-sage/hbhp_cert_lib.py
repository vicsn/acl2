import sys, time
from sympy import *
a,d,ma,mb,x1,y1,x2,y2,u1,v1,u2,v2,lam,u3,v3,x3,y3=symbols('a d ma mb x1 y1 x2 y2 u1 v1 u2 v2 lam u3 v3 x3 y3')
ALL=[a,d,ma,mb,x1,y1,x2,y2,u1,v1,u2,v2,lam,u3,v3,x3,y3]
denp=1+d*x1*x2*y1*y2; denm=1-d*x1*x2*y1*y2
C1=a*x1**2+y1**2-1-d*x1**2*y1**2; C2=a*x2**2+y2**2-1-d*x2**2*y2**2
# defining gens in definition order: (var, gen)
defs=[(ma,(a-d)*ma-2*(a+d)),(mb,(a-d)*mb-4),
      (x3,denp*x3-(x1*y2+y1*x2)),(y3,denm*y3-(y1*y2-a*x1*x2)),
      (u1,(1-y1)*u1-(1+y1)),(u2,(1-y2)*u2-(1+y2)),
      (v1,x1*v1-u1),(v2,x2*v2-u2),
      (lam,(u2-u1)*lam-(v2-v1)),
      (u3,mb*lam**2-ma-u1-u2-u3),
      (v3,(u1-u3)*lam-(v1+v3))]
def certify(goal, name):
    t=time.time()
    g=expand(goal); mult=[]; cofs={}
    for var,gen in reversed(defs):
        P=Poly(g,var); H=Poly(gen,var)
        L=H.LC(); dg=P.degree()
        if dg<=0: cofs[var]=0; continue
        k=dg-H.degree()+1
        q,r=pdiv(P,H)  # L^k * P = q*H + r
        # scale existing cofs
        Lk=expand(L**k)
        for kk in cofs: cofs[kk]=expand(cofs[kk]*Lk)
        cofs[var]=q.as_expr()
        mult.append((L,k))
        g=expand(r.as_expr())
        print(name,var,'k',k,'terms',len(Add.make_args(g)),file=sys.stderr)
    # now reduce by curve over Q(a,d)
    K=QQ.frac_field(a,d)
    (q1,q2),r=reduced(g,[C1,C2],x1,x2,y1,y2,order='lex',domain=K)
    assert r==0, ('nonzero remainder',r)
    # clear denominators
    den=lcm(fraction(together(q1))[1],fraction(together(q2))[1])
    den=factor(den)
    q1=expand(cancel(q1*den)); q2=expand(cancel(q2*den))
    for kk in cofs: cofs[kk]=expand(cofs[kk]*den)
    cofs['C1']=q1; cofs['C2']=q2
    print(name,'den',den,'time',time.time()-t,file=sys.stderr)
    return mult,den,cofs
if __name__=='__main__':
    for nm,goal in [('u',(1-y3)*u3-(1+y3)),('v',x3*v3-u3)]:
        mult,den,cofs=certify(goal,nm)
        print(nm,mult,den,{k:len(Add.make_args(v)) for k,v in cofs.items()})

def mono_to_acl2(coeff, monom, gens):
    fs=[]
    for g,e in zip(gens,monom):
        if e==1: fs.append(str(g))
        elif e>1: fs.append('(expt %s %d)'%(g,e))
    c=int(coeff)
    if not fs: return str(c)
    t=fs[-1]
    for f in reversed(fs[:-1]): t='(* %s %s)'%(f,t)
    if c!=1: t='(* %d %s)'%(c,t)
    return t
def balanced(terms):
    if not terms: return '0'
    if len(terms)==1: return terms[0]
    m=len(terms)//2
    return '(+ %s %s)'%(balanced(terms[:m]),balanced(terms[m:]))
def to_acl2(e):
    e=expand(e)
    if e==0: return '0'
    P=Poly(e,*ALL)
    assert all(c.is_integer for c in P.coeffs()), 'non-integer coeff'
    return balanced([mono_to_acl2(c,m,ALL) for m,c in P.terms()])
def sexp(e):
    # structural (unexpanded) printing for goals/gens
    e=sympify(e)
    if e.is_Integer: return str(int(e))
    if e.is_Symbol: return str(e)
    if e.is_Add:
        args=list(e.args); t=sexp(args[-1])
        for x in reversed(args[:-1]): t='(+ %s %s)'%(sexp(x),t)
        return t
    if e.is_Mul:
        args=list(e.args); t=sexp(args[-1])
        for x in reversed(args[:-1]): t='(* %s %s)'%(sexp(x),t)
        return t
    if e.is_Pow:
        assert e.exp.is_Integer and e.exp>0
        return '(expt %s %d)'%(sexp(e.base),int(e.exp))
    raise Exception(e)
