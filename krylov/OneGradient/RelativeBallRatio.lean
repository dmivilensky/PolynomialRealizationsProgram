import krylov.OneGradient.RelativeBallFibre
import krylov.OneGradient.TrialMinimax
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(c), exact arbitrary-centre ratio bound.
Use: control the genuine endpoint CG length ratio uniformly over all original
information fibres meeting a given subunit relative base ball.
Source: exact physical relative-budget/Loewner comparison and the proved actual
last CG direction curvature on the original last-Jacobi-pivot fibre.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Information
variable {n : ℕ}

/-- Every two physical completions in an arbitrary-centre relative ball have
the source's uniform last-CG-length ratio bound.
Use: the bound holds on every actual information fibre, including its two
attained extreme completions, with no assumption that the centre shares the information.
Article: main_krylov, s5:fibre(c), r≤(1+rho)/(1-rho).
Proof: both physical curvatures along the actual common last CG direction lie
between 1±rho times the same positive centre curvature. The actual last
curvature formula cancels its nonzero genuine normal coefficient. -/
theorem relative_ball_fibre_ratio
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    {rho : ℝ} (hrho : 0≤rho) (hsmall : rho<1) (blo bhi : ℝ)
    (hlo : relativeBudget center (lanczosCompletion A hA g hg hc blo-center)≤rho)
    (hhi : relativeBudget center (lanczosCompletion A hA g hg hc bhi-center)≤rho) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    (bhi-sigma)/(blo-sigma)≤(1+rho)/(1-rho) := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let d := CG.direction (cgOperator A) g n
  let v := WithLp.ofLp d
  let z := lastLanczosVector A hA g hg hc
  let gamma := inner ℝ z (CG.gradient (cgOperator A) g n)
  have hgamma : gamma≠0 := (last_cg_gradient_normal A hA g hg hc).2
  have hcurv (b : ℝ) :
      v ⬝ᵥ (lanczosCompletion A hA g hg hc b*ᵥ v)=gamma^2*(b-sigma) := by
    have he := completion_last_curvature A hA g hg hc b
    change inner ℝ d (cgOperator (lanczosCompletion A hA g hg hc b) d)=
      gamma^2*(b-lastJacobiPivot A hA g hg hc+(lastInversePivot A hA g hg hc)⁻¹) at he
    simp only [cgOperator,Matrix.inner_toEuclideanCLM] at he
    change _=gamma^2*(b-sigma)
    rw [he]
    dsimp only [sigma]
    ring
  have hsym (b : ℝ) : (lanczosCompletion A hA g hg hc b).IsSymm := by
    simp only [lanczosCompletion,Matrix.IsSymm,transpose_add,transpose_smul,
      transpose_vecMulVec,hA.1.isSymm.eq]
  have hlow := (relative_displacement_base center _ hcenter (hsym blo) hrho hsmall hlo).1
  have hupp := (relative_displacement_base center _ hcenter (hsym bhi) hrho hsmall hhi).2.1
  have hl := (Matrix.le_iff.mp hlow).dotProduct_mulVec_nonneg v
  have hh := (Matrix.le_iff.mp hupp).dotProduct_mulVec_nonneg v
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul,hcurv] at hl hh
  have hden : 0<blo-sigma := sub_pos.mpr (relative_ball_fibre_positive A hA g hg hc center hcenter hrho hsmall blo hlo)
  dsimp only
  apply (div_le_div_iff₀ hden (sub_pos.mpr hsmall)).mpr
  have h1 := mul_le_mul_of_nonneg_left (show gamma^2*(bhi-sigma)≤(1+rho)*(v ⬝ᵥ (center*ᵥ v)) by linarith)
    (sub_nonneg.mpr hsmall.le)
  have h2 := mul_le_mul_of_nonneg_left (show (1-rho)*(v ⬝ᵥ (center*ᵥ v))≤gamma^2*(blo-sigma) by linarith)
    (show 0≤1+rho by linarith)
  have hscaled : gamma^2*((bhi-sigma)*(1-rho))≤gamma^2*((1+rho)*(blo-sigma)) := by nlinarith
  exact (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hgamma)).mp hscaled

/-- The true harmonic relative-trial minimax coefficient on every information
interval inside an arbitrary-centre relative ball is at most its radius.
Use: supply the uniform one-gradient upper coefficient before specializing to
the central information, where equality is actually attained.
Article: main_krylov, s5:fibre(c) and cor:quant(b), uniform fibrewise coefficient.
Proof: the genuine physical ratio bound and positive endpoint pivots imply
the monotone condition-ratio expression (r-1)/(r+1) is at most rho. -/
theorem relative_ball_fibre_trial_value
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    {rho : ℝ} (hrho : 0≤rho) (hsmall : rho<1) (blo bhi : ℝ)
    (hlo : relativeBudget center (lanczosCompletion A hA g hg hc blo-center)≤rho)
    (hhi : relativeBudget center (lanczosCompletion A hA g hg hc bhi-center)≤rho) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    intervalMinimaxValue (1/(bhi-sigma)) (1/(blo-sigma))≤rho := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  have h1 : 0<blo-sigma := sub_pos.mpr (relative_ball_fibre_positive A hA g hg hc center hcenter hrho hsmall blo hlo)
  have h2 : 0<bhi-sigma := sub_pos.mpr (relative_ball_fibre_positive A hA g hg hc center hcenter hrho hsmall bhi hhi)
  have he : (1/(blo-sigma))/(1/(bhi-sigma))=(bhi-sigma)/(blo-sigma) := by field_simp
  have hratio := relative_ball_fibre_ratio A hA g hg hc center hcenter hrho hsmall blo bhi hlo hhi
  dsimp only at hratio ⊢
  rw [interval_minimax_ratio (one_div_pos.mpr h2),he]
  have hpos : 0<(bhi-sigma)/(blo-sigma) := div_pos h2 h1
  apply (div_le_iff₀ (by linarith : 0<(bhi-sigma)/(blo-sigma)+1)).mpr
  have hh := (le_div_iff₀ (sub_pos.mpr hsmall)).mp hratio
  nlinarith

end
end krylov.OneGradient
