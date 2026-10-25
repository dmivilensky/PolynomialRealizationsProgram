import polyak.Numerics.Parametric.LinearSolve
import polyak.Numerics.Parametric.DerivativeEnclosure

/-! Article: central-family derivative reserves. Literal derivative enclosures
are checked separately against source AD, then reused in the verified linear solve. -/
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def sourceSlopeCheck (I : IntervalRat) (cert : WeightedCertificate 7)
    (a r : Fin 7 → ℚ) (J : Matrix (Fin 7) (Fin 7) IntervalRat)
    (p : Fin 7 → IntervalRat) : Bool :=
  let X:=coordinateBox cert.center cert.radius
  let V:=coordinateBox a r
  let du:=(X 0).add (I.mul (V 0))
  let weights:=(V 5).add (V 6)
  linearSolutionCheck J p a r cert.preconditioner (2/5) &&
    decide (-1<du.lo) && decide (du.hi<1) && decide (0<weights.lo)

noncomputable section

theorem sourceSlopeCheck_sound (F : Fin 7 → Expr) (hF : ∀ i,ADSupported (F i))
    (I : IntervalRat) (cert : WeightedCertificate 7) (a r : Fin 7 → ℚ)
    (J : Matrix (Fin 7) (Fin 7) IntervalRat) (p : Fin 7 → IntervalRat)
    (cfg : DyadicConfig)
    (henc : derivativeEnclosureCheck F I (coordinateBox cert.center cert.radius) J p cfg=true)
    (hc : sourceSlopeCheck I cert a r J p=true)
    {s : ℝ} {x v : Fin 7 → ℝ} (hs : s∈I)
    (hx : FinBoxMem x (coordinateBox cert.center cert.radius))
    (he : (jacobian F s x).mulVec v= -parameterDerivative F s x) :
    |x 0+s*v 0|<1 ∧ 0<v 5+v 6 := by
  simp only [sourceSlopeCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hlinear,hlo⟩,hhi⟩,hw⟩:=hc
  have hd:=derivativeEnclosureCheck_sound F hF I _ J p cfg henc hs hx
  have hV:=linearSolutionCheck_sound J p a r cert.preconditioner (2/5) hlinear
    (jacobian F s x) (parameterDerivative F s x) v hd.1 hd.2 he
  have hdu:=IntervalRat.mem_add (hx 0) (IntervalRat.mem_mul hs (hV 0))
  have hweights:=IntervalRat.mem_add (hV 5) (hV 6)
  refine ⟨abs_lt.mpr ⟨?_,?_⟩,?_⟩
  · exact lt_of_lt_of_le (by exact_mod_cast hlo) hdu.1
  · exact lt_of_le_of_lt hdu.2 (by exact_mod_cast hhi)
  · exact lt_of_lt_of_le (by exact_mod_cast hw) hweights.1

end
end polyak.Boundary.P5
