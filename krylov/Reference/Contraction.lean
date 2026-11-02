import krylov.Reference.EnergyMinimum

/-!
Article: Lemma B.5 [apB:lem:nostag] of krylov.tex.
Use: obtain the actual positive energy-drop lower bound on every positive spectral interval.
Source: the classical admissible linear-polynomial competitor (Meurant06).
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- Parseval for the actual canonical polynomial vector, without a nonzero-reference restriction.
Use: compare admissible polynomial energies also in degenerate and terminal regimes.
Article: main_krylov, apB:lem:nostag, spectral energy comparison.
Proof: expand in the true orthonormal eigenbasis and use the already proved polynomial coordinate identity. -/
theorem canonicalPolynomial_parseval (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (p : ℝ[X]) :
    ‖canonicalPolynomial base g p‖^2=
      ∑ i : Fin n, (inner ℝ (hb.1.eigenvectorBasis i) (cgCanonicalError base g 0))^2*
        (p.eval (hb.1.eigenvalues i))^2 := by
  have he := EuclideanSpace.real_norm_sq_eq (hb.1.eigenvectorBasis.repr (canonicalPolynomial base g p))
  rw [hb.1.eigenvectorBasis.repr.norm_map] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrthonormalBasis.repr_apply_apply, canonicalPolynomial_coordinate base hb]
  ring

/-- A uniform scalar multiplier bound on the true spectrum bounds its actual polynomial energy action.
Use: admits the true residual polynomial times the classical one-step contraction polynomial.
Article: main_krylov, apB:lem:nostag.
Proof: each spectral energy weight is a nonnegative squared coordinate. -/
theorem canonicalPolynomial_mul_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (p q : ℝ[X]) {rho : ℝ} (hr : 0≤rho)
    (hp : ∀ i : Fin n, |p.eval (hb.1.eigenvalues i)|≤rho) :
    ‖canonicalPolynomial base g (p*q)‖^2≤rho^2*‖canonicalPolynomial base g q‖^2 := by
  -- Comparison is termwise in the genuine energy coordinates, so zero spectral weights need no exception.
  rw [canonicalPolynomial_parseval base hb, canonicalPolynomial_parseval base hb, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [eval_mul, mul_pow]
  have hs : (p.eval (hb.1.eigenvalues i))^2≤rho^2 :=
    by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr (hp i)
  have hc := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (sq_nonneg (inner ℝ (hb.1.eigenvectorBasis i) (cgCanonicalError base g 0)))
      (sq_nonneg (q.eval (hb.1.eigenvalues i))))
  nlinarith

/-- The classical degree-one competitor contracts uniformly on a positive interval.
Use: establishes the exact interval constant before applying the CG minimum.
Article: main_krylov, apB:lem:nostag, rho=(L−μ)/(L+μ).
Proof: the two endpoint inequalities follow by multiplication by the positive interval sum. -/
theorem linear_interval_bound {mu upper t : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (ht : mu≤t ∧ t≤upper) : |1-2/(upper+mu)*t|≤(upper-mu)/(upper+mu) := by
  have hd : 0<upper+mu := by linarith
  have he : 1-2/(upper+mu)*t=(upper+mu-2*t)/(upper+mu) := by field_simp
  rw [he, abs_le]
  constructor
  · rw [← neg_div, div_le_div_iff_of_pos_right hd]
    linarith [ht.2]
  · rw [div_le_div_iff_of_pos_right hd]
    linarith [ht.1]

/-- The genuine next CG squared error contracts by the classical interval factor.
Use: a quantitative no-stagnation bound follows from the actual CG minimum.
Article: main_krylov, apB:lem:nostag.
Proof: the actual current residual times the normalized linear interval
polynomial is admissible at the next step; its spectral multiplier bound gives the result. -/
theorem cg_error_contract_sq (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    {k : ℕ} (hk : k<referenceAtomCount base hb g) :
    ‖cgCanonicalError base g (k+1)‖^2≤((upper-mu)/(upper+mu))^2*‖cgCanonicalError base g k‖^2 := by
  -- The competitor is formed from the actual current CG polynomial, without fixing a terminal polynomial in advance.
  let p : ℝ[X] := 1-C (2/(upper+mu))*X
  let r := CG.residualPolynomial (cgOperator base) g k
  have hd : p.natDegree≤1 := by
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (by simpa using natDegree_C_mul_le (2/(upper+mu)) (X : ℝ[X])))
  have hdr : (p*r).natDegree≤k+1 := by
    have hr := (CG.polynomial_degree (cgOperator base) g k).1
    change r.natDegree≤k at hr
    exact (natDegree_mul_le (p := p) (q := r)).trans (by change p.natDegree+r.natDegree≤k+1; omega)
  have hzero : (p*r).eval 0=1 := by
    simp only [eval_mul, p, eval_sub, eval_one, eval_C, eval_X, mul_zero, sub_zero,
      r, CG.residualPolynomial_zero, mul_one]
  have he := cg_energy_minimum base hb g (by omega : k+1≤referenceAtomCount base hb g) hdr hzero
  have hc := canonicalPolynomial_mul_bound base hb g p r
    (div_nonneg (sub_nonneg.mpr hmu) (by linarith : 0≤upper+mu))
    (fun i => by simpa only [p, eval_sub, eval_one, eval_mul, eval_C, eval_X]
      using linear_interval_bound hm hmu (hspec i))
  have hcr : canonicalPolynomial base g r=cgCanonicalError base g k := canonicalPolynomial_residual base g k
  rw [hcr] at hc
  exact he.trans hc

/-- Actual CG contracts its energy error norm by the exact classical spectral interval factor.
Use: this is the printed norm form of no stagnation on [μ,L].
Article: main_krylov, apB:lem:nostag, ‖ê_(k+1)‖≤rho‖ê_k‖.
Proof: compare the nonnegative square roots of the established squared norm inequality. -/
theorem cg_error_contract (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    {k : ℕ} (hk : k<referenceAtomCount base hb g) :
    ‖cgCanonicalError base g (k+1)‖≤(upper-mu)/(upper+mu)*‖cgCanonicalError base g k‖ := by
  have he := cg_error_contract_sq base hb g hm hmu hspec hk
  have hr : 0≤(upper-mu)/(upper+mu) := div_nonneg (sub_nonneg.mpr hmu) (by linarith)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp
  simpa only [mul_pow] using he

/-- Every actual energy drop has the sharp elementary positive-interval lower bound.
Use: quantitative line and step lower bounds for later uniform perturbation arguments.
Article: main_krylov, apB:lem:nostag, c_k≥4Lμ/(L+μ)² ‖ê_k‖².
Proof: subtract the proved squared contraction from the exact computed energy-drop identity. -/
theorem cgEnergy_lower (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    {k : ℕ} (hk : k<referenceAtomCount base hb g) :
    4*upper*mu/(upper+mu)^2*‖cgCanonicalError base g k‖^2≤cgEnergy base g k := by
  have he := cg_error_contract_sq base hb g hm hmu hspec hk
  have hd : upper+mu≠0 := ne_of_gt (by linarith)
  have hc : 1-((upper-mu)/(upper+mu))^2=4*upper*mu/(upper+mu)^2 := by
    field_simp
    ring
  rw [cgEnergy_drop base hb, ← hc]
  nlinarith

/-- The article's simpler inverse-condition-number lower bound follows on every positive interval.
Use: provides c_k≥κ⁻¹‖ê_k‖² with κ=L/μ, including the singleton interval.
Article: main_krylov, apB:lem:nostag, the second energy-drop inequality.
Proof: the interval sum is at most twice its upper endpoint, so the sharper bound dominates μ/L. -/
theorem cgEnergy_lower_condition (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    {k : ℕ} (hk : k<referenceAtomCount base hb g) :
    mu/upper*‖cgCanonicalError base g k‖^2≤cgEnergy base g k := by
  -- Clear only the two positive interval denominators in the scalar comparison.
  have hu : 0<upper := hm.trans_le hmu
  have hs : 0<upper+mu := by linarith
  have hsq : (upper+mu)^2≤4*upper^2 := by
    have he := (sq_le_sq₀ hs.le (by positivity : 0≤2*upper)).mpr (by linarith : upper+mu≤2*upper)
    nlinarith
  have hc : mu/upper≤4*upper*mu/(upper+mu)^2 := by
    apply (div_le_div_iff₀ hu (sq_pos_of_pos hs)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hm.le]
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (cgEnergy_lower base hb g hm hmu hspec hk)

end
end krylov.Reference
