import polyak.Certificates.P2Codes
import polyak.Numerics.RationalExpr

/-! Article: (p5arc), executable algebraic endpoint source graphs.
Each literal pair is definitionally equal to the previously proved P2 source
representation. No rational identity or root location is assumed here. -/
namespace polyak.Certificates.Continuation.P5EndpointGraphs
open LeanCert.Core LeanCert.Engine Numerics

def G : Expr := .mul
  (polynomialExpr (⟨#[4,0,0,0,1]⟩ : QPoly) (.var 0))
  (.inv (polynomialExpr (⟨#[0,-16,0,8]⟩ : QPoly) (.var 0)))

theorem G_exact : G=Boundary.P2.GCode.expression := rfl

def u : Expr := .mul
  (polynomialExpr (⟨#[4,-8,8,-4,1]⟩ : QPoly) (.var 0))
  (.inv (polynomialExpr (⟨#[-4,0,0,0,1]⟩ : QPoly) (.var 0)))

theorem u_exact : u=Boundary.P2.uCode.expression := rfl

def atomA : Expr := .mul
  (polynomialExpr (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) (.var 0))
  (.inv (polynomialExpr (⟨#[0,-8,0,0,0,2]⟩ : QPoly) (.var 0)))

theorem atomA_exact : atomA=Boundary.P2.atomACode.expression := rfl

def atomB : Expr := .mul
  (polynomialExpr (⟨#[0,-24,40,-32,20,-6]⟩ : QPoly) (.var 0))
  (.inv (polynomialExpr (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly) (.var 0)))

theorem atomB_exact : atomB=Boundary.P2.atomBCode.expression := rfl

def meanCosine : Expr := .mul
  (polynomialExpr (⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ : QPoly) (.var 0))
  (.inv (polynomialExpr (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly) (.var 0)))

theorem meanCosine_exact : meanCosine=Boundary.P2.meanCosineCode.expression := rfl

def d : Expr := .mul
  (polynomialExpr (⟨#[5120,-32768,86016,-48128,-340736,1217024,-2326528,3164928,-3386496,3008896,-2288128,1504448,-846624,395616,-145408,38032,-5324,-376,336,-64,5]⟩ : QPoly) (.var 0))
  (.inv (polynomialExpr (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly) (.var 0)))

theorem d_exact : d=Boundary.P2.dCode.expression := rfl

def W : Expr := .mul
  (polynomialExpr (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) (.var 0))
  (.inv (polynomialExpr (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly) (.var 0)))

theorem W_exact : W=Boundary.P2.WCode.expression := rfl

end polyak.Certificates.Continuation.P5EndpointGraphs
