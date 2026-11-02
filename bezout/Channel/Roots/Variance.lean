import bezout.Channel.Roots.FiniteProduct

/-!
Article: bezout, Proposition D.1, exact finite-noise variance product.
Use: independent actual fair channel signs give the full second moment of the
finite root-step output, with all perturbation orders retained.
Proof: independence factors the product expectation; each affine sign factor
has mean its constant term and second moment the sum of its squared coefficients.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial MeasureTheory ProbabilityTheory
open scoped BigOperators
open bezout.Probability

/-- One scalar affine factor driven by the actual sign at its own oracle call. -/
def signFactor {N : ℕ} (A B : Fin N → ℝ) (s : Fin N) (ω : Fin N → Bool) : ℝ :=
  A s+B s*SignProducts.sign s ω

/-- Exact mean of one affine fair-sign factor. -/
theorem integral_signFactor {N : ℕ} (A B : Fin N → ℝ) (s : Fin N) :
    (∫ ω,signFactor A B s ω ∂Signs.law N)=A s := by
  unfold signFactor
  rw [integral_add (SignProducts.integrable_scalar _) (SignProducts.integrable_scalar _),integral_const,integral_const_mul,
    show (∫ ω, SignProducts.sign s ω ∂Signs.law N)=0 from Signs.error_integral 1 s]
  simp

/-- Exact second moment of one affine fair-sign factor. -/
theorem integral_signFactor_sq {N : ℕ} (A B : Fin N → ℝ) (s : Fin N) :
    (∫ ω,signFactor A B s ω^2 ∂Signs.law N)=A s^2+B s^2 := by
  have he : (fun ω : Fin N → Bool => signFactor A B s ω^2)=
      fun ω => A s^2+B s^2+(2*A s*B s)*SignProducts.sign s ω := by
    funext ω
    unfold signFactor
    have hs := SignProducts.sign_sq s ω
    nlinarith
  rw [he,integral_add (SignProducts.integrable_scalar _) (SignProducts.integrable_scalar _),integral_const,integral_const_mul,
    show (∫ ω, SignProducts.sign s ω ∂Signs.law N)=0 from Signs.error_integral 1 s]
  simp

/-- Independence factors the exact finite affine-sign mean. -/
theorem integral_prod_signFactor {N : ℕ} (A B : Fin N → ℝ) :
    (∫ ω,∏ s,signFactor A B s ω ∂Signs.law N)=∏ s,A s := by
  have hi : iIndepFun (signFactor A B) (Signs.law N) :=
    iIndepFun_pi (fun s => (measurable_of_finite (fun b => A s+B s*Signs.value 1 b)).aemeasurable)
  rw [hi.integral_fun_prod_eq_prod_integral (fun s => (measurable_of_finite (signFactor A B s)).stronglyMeasurable.aestronglyMeasurable)]
  simp only [integral_signFactor]

/-- Independence factors the full finite affine-sign second moment. -/
theorem integral_prod_signFactor_sq {N : ℕ} (A B : Fin N → ℝ) :
    (∫ ω,(∏ s,signFactor A B s ω)^2 ∂Signs.law N)=∏ s,(A s^2+B s^2) := by
  have hi : iIndepFun (fun s ω => signFactor A B s ω^2) (Signs.law N) :=
    iIndepFun_pi (fun s => (measurable_of_finite (fun b => (A s+B s*Signs.value 1 b)^2)).aemeasurable)
  have hp (ω : Fin N → Bool) : (∏ s,signFactor A B s ω)^2=∏ s,signFactor A B s ω^2 := by
    rw [Finset.prod_pow]
  simp_rw [hp]
  rw [hi.integral_fun_prod_eq_prod_integral (fun s => (measurable_of_finite
    (fun ω => signFactor A B s ω^2)).stronglyMeasurable.aestronglyMeasurable)]
  simp only [integral_signFactor_sq]

/-- The nominal multiplier is the exact mean of the full finite-noise root product. -/
theorem finiteMultiplier_mean {N : ℕ} (α : Fin N → ℝ) (lam δ : ℝ) :
    (∫ ω,finiteMultiplier α lam δ (fun s => SignProducts.sign s ω) ∂Signs.law N)=
      (terminal α).eval lam := by
  have hp : (fun ω : Fin N → Bool => finiteMultiplier α lam δ (fun s => SignProducts.sign s ω))=
      fun ω => ∏ s, signFactor (fun s => 1-α s*lam) (fun s => -δ*α s) s ω := by
    funext ω
    unfold finiteMultiplier
    apply Finset.prod_congr rfl
    intro s _
    unfold signFactor
    ring
  rw [hp,integral_prod_signFactor]
  simp [terminal,eval_prod]

/-- The full second moment is the product of the per-call squared nominal and noisy factors. -/
theorem finiteMultiplier_second_moment {N : ℕ} (α : Fin N → ℝ) (lam δ : ℝ) :
    (∫ ω,finiteMultiplier α lam δ (fun s => SignProducts.sign s ω)^2 ∂Signs.law N)=
      ∏ s,((1-α s*lam)^2+δ^2*α s^2) := by
  have hp : (fun ω : Fin N → Bool => finiteMultiplier α lam δ (fun s => SignProducts.sign s ω)^2)=
      fun ω => (∏ s, signFactor (fun s => 1-α s*lam) (fun s => -δ*α s) s ω)^2 := by
    funext ω
    congr 1
    unfold finiteMultiplier
    apply Finset.prod_congr rfl
    intro s _
    unfold signFactor
    ring
  rw [hp,integral_prod_signFactor_sq]
  apply Finset.prod_congr rfl
  intro s _
  ring

/-- The exact finite variance of one spectral multiplier, without truncating higher orders. -/
theorem finiteMultiplier_variance {N : ℕ} (α : Fin N → ℝ) (lam δ : ℝ) :
    (∫ ω,(finiteMultiplier α lam δ (fun s => SignProducts.sign s ω)-(terminal α).eval lam)^2 ∂Signs.law N)=
      (∏ s,((1-α s*lam)^2+δ^2*α s^2))-(terminal α).eval lam^2 := by
  have hp : (fun ω : Fin N → Bool =>
      (finiteMultiplier α lam δ (fun s => SignProducts.sign s ω)-(terminal α).eval lam)^2)=
      fun ω => finiteMultiplier α lam δ (fun s => SignProducts.sign s ω)^2-
        (2*(terminal α).eval lam)*finiteMultiplier α lam δ (fun s => SignProducts.sign s ω)+
        (terminal α).eval lam^2 := by funext ω; ring
  rw [hp,integral_add (SignProducts.integrable_scalar _) (SignProducts.integrable_scalar _),integral_sub (SignProducts.integrable_scalar _) (SignProducts.integrable_scalar _),
    integral_const_mul,finiteMultiplier_second_moment,finiteMultiplier_mean,integral_const]
  simp
  ring

/-- The exact variance of finitely many actual commuting-channel output coordinates. -/
theorem history_mode_variance {ι : Type*} [Fintype ι] {N : ℕ} (α : Fin N → ℝ)
    (eig : ι → ℝ) (initial : ι → ℝ) (δ : ℝ) :
    (∫ ω,∑ j,(((history α).oracleOutput initial
      (modeOracle eig δ (fun s => SignProducts.sign s ω))) j-(terminal α).eval (eig j)*initial j)^2 ∂Signs.law N)=
    ∑ j,initial j^2*((∏ s,((1-α s*eig j)^2+δ^2*α s^2))-(terminal α).eval (eig j)^2) := by
  rw [integral_finsetSum _ (by intro j _; exact SignProducts.integrable_scalar _)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [history_mode_product]
  have hp : (fun ω : Fin N → Bool =>
      (finiteMultiplier α (eig j) δ (fun s => SignProducts.sign s ω)*initial j-
        (terminal α).eval (eig j)*initial j)^2)=
      fun ω => initial j^2*(finiteMultiplier α (eig j) δ (fun s => SignProducts.sign s ω)-
        (terminal α).eval (eig j))^2 := by funext ω; ring
  rw [hp,integral_const_mul,finiteMultiplier_variance]

end
end bezout.Channel.Roots
