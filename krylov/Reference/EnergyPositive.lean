import krylov.Reference.Energy

set_option autoImplicit false
/-!
Article: main_krylov, s2:eq:cg and thm:select, genuine active reference energy domains.
Use: justify real active CG energy, square-root and line-length
divisions by the actual source active atom count.
Source: genuine nonstagnating computed CG steps, true canonical energy
identity and real exact-search energy/line/residual relation.
-/

namespace krylov.Reference
noncomputable section
open krylov.Secant
variable {n : ℕ}

/-- Every genuine computed CG step before the actual active atom count has strictly positive true energy.
Use: Every genuine computed CG step before the actual active atom count has strictly positive true energy.
Article: main_krylov, s2:eq:cg and thm:select, genuine active reference energy domains.
Proof: Actual nonstagnation gives a genuine nonzero canonical step; its real squared norm equals the true physical energy. -/
theorem cgEnergy_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g) :
    0<cgEnergy base g k := by
  rw [cgEnergy_eq_norm_sq base hb]
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero base hb g k (fun i hi => cg_nonstagnation base hb g i (hi.trans_lt hk))))

/-- Every genuine computed CG exact-search line length before the true active atom count is strictly positive.
Use: Every genuine computed CG exact-search line length before the true active atom count is strictly positive.
Article: main_krylov, s2:eq:cg and thm:select, genuine active reference energy domains.
Proof: The actual positive step energy equals the true line length times the genuine positive residual norm squared. -/
theorem cgLength_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g) :
    0<CG.length (cgOperator base) g k := by
  have he := cgEnergy_eq_length_norm base hb g hk
  have hc := cgEnergy_pos base hb g k hk
  have hn : 0<‖CG.gradient (cgOperator base) g k‖^2 := sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr (cg_nonstagnation base hb g k hk))
  nlinarith
end
end krylov.Reference
