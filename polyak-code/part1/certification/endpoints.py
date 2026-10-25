"""Endpoint connections using rational P2, without its obsolete continuation."""
import sympy as s
from flint import arb
from .certificates.p2 import model
from .interval import funcs,inside
from .algebra.systems import p1,z
from .precision import local_precision


@local_precision(bits=256,digits=90)
def check(ctx):
    data = model(False)
    variable = data["z"]

    def rational(q):
        return arb(int(s.numer(q)))/int(s.denom(q))

    def isolate(poly,lo,hi):
        intervals = s.Poly(poly,variable).intervals(eps=s.Rational(1,10**65),inf=s.Rational(lo),sup=s.Rational(hi))
        ctx.check(len(intervals)==1 and intervals[0][1]==1,"rational P2 endpoint is isolated and simple")
        a,b = map(rational,intervals[0][0])
        return arb((a+b)/2,(b-a)/2)

    def identify(family,parameter,point):
        boxes = ctx.artifacts[family+"_boxes.json"]
        for box in boxes:
            if parameter.lower()>=arb(str(box["a"])) and parameter.upper()<=arb(str(box["b"])):
                X = [arb(arb(str(c)),arb(str(r))) for c,r in zip(box["center"],box["radii"])]
                ctx.check(all(inside(v,w) for v,w in zip(point,X)),family+": exact endpoint is in a certified branch box",kind="arb")
                return
        raise ValueError("no continuation box contains the exact "+family+" endpoint")

    _,variables,equations,_,_ = p1()
    zw = s.sqrt(3)-1
    ctx.check(all(s.simplify(e.subs({z:zw,variables[0]:0,variables[1]:-1/(2*zw)}))==0 for e in equations),
              "P1 and spiral meet at the exact quadratic endpoint")
    zwi = arb(3).sqrt()-1
    identify("p1",zwi,[arb(0),-1/(2*zwi)])
    z1 = isolate(data["f1"],"1.6956","1.6957")
    za = isolate(data["N12"],"1.6989","1.699")
    ctx.check(z1<za,"rational P2 endpoints are correctly ordered",kind="arb")
    values = {name:funcs(data[name],(variable,))(za) for name in ("G","u","a","b","mc","d","W")}
    discriminant = values["a"]**2-4*values["b"]
    ctx.check(discriminant>0,"endpoint atom discriminant is positive",kind="arb")
    x = (-values["a"]-discriminant.sqrt())/2
    y = (-values["a"]+discriminant.sqrt())/2
    p = (values["mc"]-x)/(y-x)
    h = values["G"]-1
    point = [(values["u"]-arb(".5"))/h,(x+arb(".5"))/h,y,p/h,values["d"]/h,values["W"],1-values["W"]]
    identify("central",h,point)
    ctx.check(0<p and p<1 and 0<values["W"] and values["W"]<1,"P2/P5 endpoint weights are physical",kind="arb")
