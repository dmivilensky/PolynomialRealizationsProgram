import polyak.Boundary.P5.NormalizedDual
import polyak.Boundary.P5.Active

/-!
Article: the four active primal constraints imply the missing Q(x)=0 contact.
Use: the actual system imposes Q(y)=Q′(x)=Q′(y)=0 explicitly; primal–dual
pairing supplies the main-atom value equation without an extra hypothesis.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral

/-- Article: normalized value cancellation in the actual two-atom primal–dual pairing. -/
theorem primal_dual_pairing (h : ℝ) (Z : Coordinates) :
    (1-h*Z 3)*(normalizedLower (1/2+h*Z 0) (1+h) 1 (-1/2+h*Z 1)+
      Z 5*normalizedUpper (1/2+h*Z 0) (1+h) 2 (-1/2+h*Z 1)+
      Z 6*normalizedUpper (1/2+h*Z 0) (1+h) 3 (-1/2+h*Z 1)+
      (1-Z 5-Z 6)*normalizedUpper (1/2+h*Z 0) (1+h) 5 (-1/2+h*Z 1))+
    h*Z 3*(normalizedLower (1/2+h*Z 0) (1+h) 1 (Z 2)+
      Z 5*normalizedUpper (1/2+h*Z 0) (1+h) 2 (Z 2)+
      Z 6*normalizedUpper (1/2+h*Z 0) (1+h) 3 (Z 2)+
      (1-Z 5-Z 6)*normalizedUpper (1/2+h*Z 0) (1+h) 5 (Z 2))=
    actualPrimal h Z 1 (-1)+Z 5*actualPrimal h Z 2 1+
      Z 6*actualPrimal h Z 3 1+(1-Z 5-Z 6)*actualPrimal h Z 5 1 := by
  rw [actualPrimal_lower,actualPrimal_upper,actualPrimal_upper,actualPrimal_upper]
  ring

private theorem weighted_contact {D Sx Sy p gap Q : ℝ}
    (hx : D*Sx= -gap*Q) (hy : D*Sy=0) (he : (1-p)*Sx+p*Sy=0) :
    (1-p)*gap*Q=0 := by
  linear_combination (1-p)*hx+p*hy-D*he

/-- Article: actual source solutions automatically have the fourth double-contact equation Q(x)=0. -/
theorem dualReal_main_root {h : ℝ} (hh : 0≤h) {Z : Coordinates}
    (hz : regularSystem (h,Z)=0) (hp : h*Z 3<1) (hx : -1/2+h*Z 1<1) :
    (dualReal h Z).eval (-1/2+h*Z 1)=0 := by
  have hg : (1 : ℝ)≤1+h := by linarith
  have hnx := dualClosed_normalization hg (1/2+h*Z 0) (Z 5) (Z 6) (-1/2+h*Z 1)
  have hny := dualClosed_normalization hg (1/2+h*Z 0) (Z 5) (Z 6) (Z 2)
  rw [← dualReal_closed] at hnx hny
  obtain ⟨h1,h2,h3,h5⟩ := active_slacks_zero hh hz
  have he := primal_dual_pairing h Z
  rw [h1,h2,h3,h5] at he
  simp only [mul_zero,add_zero] at he
  have hy := (regularSystem_dual_exact h Z).1
  rw [hz] at hy
  have hy' : (dualReal h Z).eval (Z 2)=0 := hy.symm
  rw [hy',mul_zero] at hny
  have hxzero : (1-h*Z 3)*(1+h-(-1/2+h*Z 1))*
      (dualReal h Z).eval (-1/2+h*Z 1)=0 := by
    exact weighted_contact hnx hny he
  have hpne : 1-h*Z 3≠0 := by linarith
  have hxne : 1+h-(-1/2+h*Z 1)≠0 := by linarith
  exact (mul_eq_zero.mp hxzero).resolve_left (mul_ne_zero hpne hxne)

end polyak.Boundary.P5
