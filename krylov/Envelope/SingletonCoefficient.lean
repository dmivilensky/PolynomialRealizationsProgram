import krylov.Envelope.FinalErrorImageNorm

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine last-nontrivial singleton coefficient.
Use: convert the actual attaining two-plane tilt product into the printed
true beta/step-energy constant and establish its genuine strict positivity.
Source: measured actual CG energy and residual-ratio identities, the
proved true two-site final-error norm and real positive square-root algebra.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
variable {n : ℕ}

/-- The genuine last-nontrivial singleton tilt product equals exactly the printed actual CG beta times square root of the three true neighboring step energies.
Use: The genuine last-nontrivial singleton tilt product equals exactly the printed actual CG beta times square root of the three true neighboring step energies.
Article: main_krylov, thm:select, genuine last-nontrivial singleton coefficient.
Proof: Square both real nonnegative quantities, substitute the genuine two-site final-error norm and actual energy/line/residual identities, then cancel only proved positive real domains. -/
theorem singleton_tilt_coefficient (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k+3<referenceAtomCount base hb g) :
    (CG.length (cgOperator base) g (k+2)*Real.sqrt (cgEnergy base g (k+1))/Real.sqrt (cgEnergy base g (k+2)))*
      ‖cgOperator base (cgCanonicalError base g (k+3))‖=
    CG.beta (cgOperator base) g (k+2)*Real.sqrt
      (cgEnergy base g (k+1)*(cgEnergy base g (k+2)+cgEnergy base g (k+3))/cgEnergy base g (k+3)) := by
  -- Keep every genuine active energy and measured CG coefficient on its true positive domain before cancellation.
  let a := CG.length (cgOperator base) g (k+2)
  let c := cgEnergy base g (k+1)
  let d := cgEnergy base g (k+2)
  let e := cgEnergy base g (k+3)
  let x := ‖CG.gradient (cgOperator base) g (k+2)‖^2
  let y := ‖CG.gradient (cgOperator base) g (k+3)‖^2
  let t := ‖cgOperator base (cgCanonicalError base g (k+3))‖
  have ha : 0<a := cgLength_pos base hb g (k+2) (by omega)
  have hc : 0<c := cgEnergy_pos base hb g (k+1) (by omega)
  have hd : 0<d := cgEnergy_pos base hb g (k+2) (by omega)
  have he : 0<e := cgEnergy_pos base hb g (k+3) hk
  have hx : 0<x := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (cg_nonstagnation base hb g (k+2) (by omega)))
  have hy : 0<y := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (cg_nonstagnation base hb g (k+3) hk))
  have hed : d=a*x := cgEnergy_eq_length_norm base hb g (by omega : k+2<referenceAtomCount base hb g)
  have ht : t^2=y^2*(d⁻¹+e⁻¹) := by
    have hh := canonical_final_error_image_norm_sq base hb g (k+2) hk
    dsimp only [t,y,d,e]
    convert! hh using 1
    ring
  have hR : 0<c*(d+e)/e := by positivity
  -- Compare the actual squared attaining product with the true squared printed coefficient, retaining genuine nonnegative square roots.
  have hs : ((a*Real.sqrt c/Real.sqrt d)*t)^2=(y/x)^2*(c*(d+e)/e) := by
    calc
      _ = a^2*c/d*t^2 := by
        rw [mul_pow,div_pow,mul_pow,Real.sq_sqrt hc.le,Real.sq_sqrt hd.le]
      _ = a^2*c/d*(y^2*(d⁻¹+e⁻¹)) := by rw [ht]
      _ = _ := by
        rw [hed]
        field_simp
        ring
  have hsR : ((y/x)*Real.sqrt (c*(d+e)/e))^2=(y/x)^2*(c*(d+e)/e) := by
    rw [mul_pow,Real.sq_sqrt hR.le]
  have hleft : 0≤(a*Real.sqrt c/Real.sqrt d)*t := by positivity
  have hright : 0≤(y/x)*Real.sqrt (c*(d+e)/e) := by positivity
  change (a*Real.sqrt c/Real.sqrt d)*t=(y/x)*Real.sqrt (c*(d+e)/e)
  nlinarith

/-- The printed actual last-nontrivial singleton selection coefficient is strictly positive before genuine active exhaustion.
Use: The printed actual last-nontrivial singleton selection coefficient is strictly positive before genuine active exhaustion.
Article: main_krylov, thm:select, genuine last-nontrivial singleton coefficient.
Proof: All three genuine step energies and both real residual norms are strictly positive on the actual active prefix. -/
theorem singleton_tilt_coefficient_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k+3<referenceAtomCount base hb g) :
    0<CG.beta (cgOperator base) g (k+2)*Real.sqrt
      (cgEnergy base g (k+1)*(cgEnergy base g (k+2)+cgEnergy base g (k+3))/cgEnergy base g (k+3)) := by
  have hc := cgEnergy_pos base hb g (k+1) (by omega)
  have hd := cgEnergy_pos base hb g (k+2) (by omega)
  have he := cgEnergy_pos base hb g (k+3) hk
  have hx : 0<‖CG.gradient (cgOperator base) g (k+2)‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (cg_nonstagnation base hb g (k+2) (by omega)))
  have hy : 0<‖CG.gradient (cgOperator base) g (k+3)‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (cg_nonstagnation base hb g (k+3) hk))
  exact mul_pos (div_pos hy hx) (Real.sqrt_pos.mpr (div_pos (mul_pos hc (add_pos hd he)) he))

end
end krylov.Envelope
