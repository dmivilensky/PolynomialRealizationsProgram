import krylov.Envelope.CanonicalPolynomialFlags
import krylov.Envelope.NormTrace

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:DK, genuine metric power-insertion Frobenius pairings.
Use: transform each true ordered physical polynomial perturbation term
into the actual canonical symmetric outer-product matrix coefficient
with its genuine shifted reference powers.
Source: standard real symmetric operator powers, actual metric-root
commutation and true symmetric perturbation Frobenius pairings.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation krylov.LinearAlgebra Polynomial Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine positive reference metric root commutes with every actual physical reference operator power.
Use: The genuine positive reference metric root commutes with every actual physical reference operator power.
Article: main_krylov, apB:lem:DK, genuine metric power-insertion Frobenius pairings.
Proof: Specialize the true polynomial commutation identity and retain the genuine continuous/linear operator power coercion. -/
theorem root_power_action (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (r : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) :
    cgOperator (metricRoot base) (((cgOperator base)^r) v)=((cgOperator base)^r) (cgOperator (metricRoot base) v) := by
  convert! root_polynomial_action base hb (X^r) v using 1 <;>
    simp only [map_pow,aeval_X,← ContinuousLinearMap.toLinearMap_pow] <;> rfl

/-- The actual root-transformed reference-gradient power equals the genuine one-higher reference power of the true canonical CG error.
Use: The actual root-transformed reference-gradient power equals the genuine one-higher reference power of the true canonical CG error.
Article: main_krylov, apB:lem:DK, genuine metric power-insertion Frobenius pairings.
Proof: Commute the real root through the actual power and use the genuine base/root dual identity. -/
theorem root_power_gradient (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N r : ℕ) :
    cgOperator (metricRoot base) (((cgOperator base)^r) (CG.gradient (cgOperator base) g N))=
      ((cgOperator base)^(r+1)) (cgCanonicalError base g N) := by
  rw [root_power_action base hb]
  have he : cgOperator (metricRoot base) (CG.gradient (cgOperator base) g N)=
      cgOperator base (cgCanonicalError base g N) := (canonical_base_dual base hb _).symm
  rw [he,pow_succ,mul_apply_eq_comp]

/-- Every true ordered physical power-insertion perturbation pairs with the actual CG gradient as the genuine canonical symmetric outer-product Frobenius coefficient.
Use: Every true ordered physical power-insertion perturbation pairs with the actual CG gradient as the genuine canonical symmetric outer-product Frobenius coefficient.
Article: main_krylov, apB:lem:DK, genuine metric power-insertion Frobenius pairings.
Proof: Move the actual symmetric left reference power through the true inner product. Genuine metric congruence and real shifted gradient-power identities give the actual canonical test vectors; use the true symmetric-action Frobenius pairing. -/
theorem power_metric_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N r s : ℕ) (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm) :
    inner ℝ ((((cgOperator base)^r)*cgOperator (metricRoot base*E*metricRoot base)*((cgOperator base)^s)) g)
      (CG.gradient (cgOperator base) g N)=
    inner ℝ (frobeniusVector E) (frobeniusVector (symmetricOuter
      (WithLp.ofLp (((cgOperator base)^(r+1)) (cgCanonicalError base g N)))
      (WithLp.ofLp (((cgOperator base)^(s+1)) (cgCanonicalError base g 0))))) := by
  -- Transfer the genuine left reference power across the actual physical inner product before applying the true metric-root congruence.
  let Q := cgOperator base
  have hr : (Q^r).toLinearMap.IsSymmetric := by
    rw [ContinuousLinearMap.toLinearMap_pow]
    exact (cgOperator_positive base hb).1.pow r
  have hp := hr (cgOperator (metricRoot base*E*metricRoot base) ((Q^s) g)) (CG.gradient Q g N)
  change inner ℝ (((Q^r)*cgOperator (metricRoot base*E*metricRoot base)*(Q^s)) g) (CG.gradient Q g N)=
    inner ℝ (cgOperator (metricRoot base*E*metricRoot base) ((Q^s) g)) ((Q^r) (CG.gradient Q g N)) at hp
  rw [hp,real_inner_comm]
  change inner ℝ ((Q^r) (CG.gradient Q g N))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base*E*metricRoot base) ((Q^s) g))=_
  rw [metric_drift_pairing]
  change inner ℝ (cgOperator (metricRoot base) ((Q^r) (CG.gradient Q g N)))
    (cgOperator E (cgOperator (metricRoot base) ((Q^s) g)))=_
  rw [root_power_gradient base hb g N r]
  have hs : cgOperator (metricRoot base) ((Q^s) g)=((cgOperator base)^(s+1)) (cgCanonicalError base g 0) :=
    root_power_gradient base hb g 0 s
  rw [hs]
  exact symmetric_action_frobenius_euclidean E hE _ _
end
end krylov.Envelope
