import krylov.Stability.UniformFCStep

/-!
Article: main_krylov, apB:lem:UAsteps, full genuine uniform FC finite induction.
Use: prove actual canonical FC step and gradient stability over every defined
finite cycle with constants depending only on its horizon and conditioning,
including arbitrarily small genuine CG reference energies.
Source: the proved actual next-step stability theorem and genuine canonical
secant accumulation; no analytic or minimum-energy compactness argument is used.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- An explicit finite uniform FC stability constant built from the genuine next-step coefficient.
Use: depends only on the horizon and spectral conditioning, not the actual quadratic reference or any individual energy drop.
Article: main_krylov, apB:lem:UAsteps, C(n,κ). -/
def fcUniformConstant (κ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => fcUniformConstant κ k+fcStepConstant k κ (fcUniformConstant κ k)

/-- Every actual finite uniform FC induction constant is nonnegative.
Use: genuine perturbation errors can be compared monotonically throughout the finite prefix.
Article: main_krylov, apB:lem:UAsteps.
Proof: induct on the real finite recurrence and use nonnegativity of each actual next-step coefficient. -/
theorem fcUniformConstant_nonneg {κ : ℝ} (hκ : 0≤κ) (k : ℕ) : 0≤fcUniformConstant κ k := by
  induction k with
  | zero => rfl
  | succ k ih => exact add_nonneg ih (fcStepConstant_nonneg k hκ ih)

/-- The actual explicit FC stability constants increase with the genuine finite horizon.
Use: earlier true step errors remain controlled by the current induction constant.
Article: main_krylov, apB:lem:UAsteps.
Proof: the true next-step coefficient added at each finite induction is nonnegative. -/
theorem fcUniformConstant_monotone {κ : ℝ} (hκ : 0≤κ) : Monotone (fcUniformConstant κ) := by
  apply monotone_nat_of_le_succ
  intro k
  change fcUniformConstant κ k≤fcUniformConstant κ k+fcStepConstant k κ (fcUniformConstant κ k)
  exact le_add_of_nonneg_right (fcStepConstant_nonneg k hκ (fcUniformConstant_nonneg hκ k))

/-- One explicit dimension-only budget radius controls every true Gram, projected-conjugacy and exact-search smallness condition in the finite FC induction.
Use: the admissible radius stays independent of actual reference energies and directions, including the empty horizon.
Article: main_krylov, apB:lem:UAsteps.
Proof: the genuine square root of each prefix dimension is at most the
horizon plus one; multiply by the true nonnegative budget and use the single
stated finite radius inequality. -/
theorem fc_uniform_radius_conditions (N k : ℕ) (hk : k≤N) {δ : ℝ} (hδ : 0≤δ)
    (hsmall : 8*((N : ℝ)+1)*δ≤1) :
    δ≤1/2 ∧ (k : ℝ)*δ≤1/2 ∧ 4*Real.sqrt k*δ≤1/2 := by
  -- The same actual budget radius covers every true prefix dimension.
  have hN : 0≤(N : ℝ) := Nat.cast_nonneg N
  have hkN : (k : ℝ)≤(N : ℝ) := by exact_mod_cast hk
  have hsqrt : Real.sqrt k≤(N : ℝ)+1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (N : ℝ)]
  have hNδ := mul_nonneg hN hδ
  have hkδ := mul_le_mul_of_nonneg_right (show (k : ℝ)≤(N : ℝ)+1 by linarith) hδ
  have hrootδ := mul_le_mul_of_nonneg_right hsqrt hδ
  constructor
  · nlinarith
  · constructor <;> nlinarith

/-- Every actually defined finite full-memory FC cycle obeys the genuine uniform canonical step bound with constants depending only on horizon and conditioning.
Use: proves the source finite real FC stability induction over all normalized positive references, including arbitrarily small CG energies and zero actual final line displacements.
Article: main_krylov, apB:lem:UAsteps, μ=1 and ‖e₀‖≤1.
Proof: induct on the actual observed prefix. The single dimension-only
radius supplies every real smallness condition, and the proved genuine
next-step estimate propagates the actual step bound. Monotone explicit
constants retain all true preceding estimates; the reference supplies only
actual CG nonstagnation, never a smallest energy denominator. -/
theorem fullFC_uniform_steps (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {κ δ : ℝ} (hκ : 1≤κ)
    (hspec : ∀ i, 1≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤κ)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0)
    (hsolve : ∀ i<N, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g i)))).det)
    (hcurv : ∀ i<N, inner ℝ (fcDirection fullMemory A g i) (A i (fcDirection fullMemory A g i))≠0)
    (hA : ∀ i<N, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ)
    (hδ : 0≤δ) (hsmall : 8*((N : ℝ)+1)*δ≤1) :
    ∀ i<N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖≤
      fcUniformConstant κ N*δ := by
  -- Each induction hypothesis concerns the actual executed steps of the same real trajectory.
  have hκ0 : 0≤κ := le_trans (by norm_num) hκ
  have hprefix : ∀ k : ℕ, k≤N → ∀ i<k,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖≤
        fcUniformConstant κ k*δ := by
    intro k
    induction k with
    | zero => intro _ i hi; omega
    | succ k ih =>
      intro hk i hi
      have hkN : k<N := by omega
      have hprev := ih hkN.le
      obtain ⟨hδhalf,hGram,hProj⟩ := fc_uniform_radius_conditions N k hkN.le hδ hsmall
      -- All actual inverse, search, span and true-CG weights were discharged in the next-step theorem.
      have hnew := fullFC_uniform_next_step base hb A g k hκ (fcUniformConstant_nonneg hκ0 k)
        hspec hinit (fun j hj => hpre j (by omega)) (fun j hj => hsolve j (by omega))
        (hcurv k hkN) (fun j hj => hA j (by omega)) hδ hδhalf hGram hProj hprev
      by_cases he : i=k
      · subst i
        apply hnew.trans
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (fcUniformConstant_nonneg hκ0 k)) hδ
      · exact (hprev i (by omega)).trans (mul_le_mul_of_nonneg_right
          (fcUniformConstant_monotone hκ0 (Nat.le_succ k)) hδ)
  exact hprefix N le_rfl

/-- The genuine defined finite FC trajectory has uniform actual canonical step and terminal-gradient bounds with the same horizon/conditioning-only constants.
Use: both the true line steps and actually accumulated residual are controlled near arbitrarily small CG energies.
Article: main_krylov, apB:lem:UAsteps.
Proof: the full true step induction supplies the actual step estimates;
the real canonical secant accumulation theorem then bounds the genuine terminal gradient. -/
theorem fullFC_uniform_trajectory (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {κ δ : ℝ} (hκ : 1≤κ)
    (hspec : ∀ i, 1≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤κ)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0)
    (hsolve : ∀ i<N, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g i)))).det)
    (hcurv : ∀ i<N, inner ℝ (fcDirection fullMemory A g i) (A i (fcDirection fullMemory A g i))≠0)
    (hA : ∀ i<N, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ)
    (hδ : 0≤δ) (hsmall : 8*((N : ℝ)+1)*δ≤1) :
    (∀ i<N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖≤
      fcUniformConstant κ N*δ) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (fcGradient fullMemory A g N)-cgCanonicalError base g N‖≤
        (N : ℝ)*(2*fcUniformConstant κ N+1)*δ := by
  have hs := fullFC_uniform_steps base hb A g N hκ hspec hinit hpre hsolve hcurv hA hδ hsmall
  refine ⟨hs,?_⟩
  have hδhalf := (fc_uniform_radius_conditions N N le_rfl hδ hsmall).1
  exact fullFC_canonical_gradient_bound base hb A g N hδ (by linarith)
    (fcUniformConstant_nonneg (le_trans (by norm_num) hκ) N) hinit hA hs

end
end krylov.Stability
