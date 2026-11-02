import krylov.Information.PlanarAdmissibility
import krylov.Secant.TerminalRadius

/-!
Article: main_krylov, thm:C, quantitative planar information radius.
Use: bound the true two-completion worst residual of every arbitrary common
terminal correction using the exact actual mean inverse and hidden diagonal.
Source: exact planar matrix actions, the genuine positive mean domain and
the existing two-scenario Hilbert-space information inequality.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant krylov.Reference krylov.LinearAlgebra krylov.Correction
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {n : ℕ}

/-- A true inverse of an operator within one half of the identity has norm at most two.
Use: bound the genuine inverse mean model in the explicit lower information radius.
Article: main_krylov, thm:C and lem:terminal-fibre, quantitative mean inverse bound.
Proof: subtract the actual model defect from M N v to reconstruct N v.
The defect action costs at most half its norm, so the norm triangle
inequality gives ‖N v‖≤2‖v‖ and hence the actual operator-norm bound.
-/
theorem inverse_operator_norm_le_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M J : V →L[ℝ] V) (hMJ : M*J=1) (hM : ‖M-1‖≤(1/2 : ℝ)) : ‖J‖≤2 := by
  -- Bound the actual inverse action before taking its genuine operator norm.
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have he : M (J v)=v := by rw [← mul_apply_eq_comp,hMJ,one_apply_eq_self]
  have hd : M (J v)-(M-1) (J v)=J v := by
    simp only [_root_.sub_apply,one_apply_eq_self]
    abel
  have ht := norm_sub_le (M (J v)) ((M-1) (J v))
  rw [hd,he] at ht
  have hb : ‖(M-1) (J v)‖≤(1/2 : ℝ)*‖J v‖ :=
    ((M-1).le_opNorm _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  linarith

/-- The actual planar cross mean defect has its true scalar spectral bound.
Use: derive the inverse mean domain and its quantitative bound from the original cross coefficient.
Article: main_krylov, thm:C, ‖M−I‖≤|x|.
Proof: scale the proved actual unit planar cross matrix and its genuine spectral norm bound. -/
theorem planar_cross_norm_le (e f : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0) (x : ℝ) :
    ‖planarMatrix e f 0 x 0‖≤|x| := by
  have hb : ‖planarMatrix e f 0 1 0‖≤1 := by
    simpa only [chebyshev1.opNorm,neg_zero] using
      planar_spectral_norm_le e f he hf hef 0 1 (by norm_num)
  have hs : planarMatrix e f 0 x 0=x • planarMatrix e f 0 1 0 := by
    simpa only [mul_zero,mul_one] using planarMatrix_scale e f x 0 1 0
  rw [hs,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg x)).trans_eq (mul_one _)

/-- The actual inverse cross mean has the exact first-column action required by the source lower radius.
Use: compute the genuine hidden-diagonal numerator without an assumed inverse or residual expansion.
Article: main_krylov, thm:C, M⁻¹e=(e−xf)/(1−x²).
Proof: the actual mean sends e to e+xf and f to f+xe. Its proposed inverse
column therefore maps exactly to e. The proved positive mean domain
justifies cancellation by the genuine matrix inverse.
-/
theorem planar_cross_inverse_e (e f : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0) (x : ℝ) (hx : |x|<1) :
    cgOperator (1+planarMatrix e f 0 x 0)⁻¹ e=(1-x^2)⁻¹ • (e-x • f) := by
  -- Derive the true mean inverse domain before solving its actual first column.
  let M := 1+planarMatrix e f 0 x 0
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (terminal_cross_posDef e f he hf hef hx).det_pos.ne'
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hff : inner ℝ f f=1 := by rw [real_inner_self_eq_norm_sq,hf,one_pow]
  have hfe : inner ℝ f e=0 := (real_inner_comm e f).trans hef
  have hMe : cgOperator M e=e+x • f := by
    simp only [M,cgOperator,map_add,map_one,_root_.add_apply,one_apply_eq_self,
      planarMatrix_action,hee,hfe,mul_zero,mul_one,zero_add,zero_smul,add_zero]
  have hMf : cgOperator M f=f+x • e := by
    simp only [M,cgOperator,map_add,map_one,_root_.add_apply,one_apply_eq_self,
      planarMatrix_action,hff,hef,mul_zero,mul_one,zero_add,zero_smul,add_zero]
  have hden : 0<1-x^2 := by nlinarith [sq_abs x,abs_nonneg x]
  have hsol : cgOperator M ((1-x^2)⁻¹ • (e-x • f))=e := by
    rw [map_smul,map_sub,map_smul,hMe,hMf]
    have hs : (e+x • f)-x • (f+x • e)=(1-x^2) • e := by module
    rw [hs,smul_smul,inv_mul_cancel₀ hden.ne',one_smul]
  have hc := congrArg (cgOperator M⁻¹) hsol
  have hi (v : EuclideanSpace ℝ (Fin n)) : cgOperator M⁻¹ (cgOperator M v)=v := by
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,nonsing_inv_mul _ hu,map_one,one_apply_eq_self]
  rw [hi] at hc
  exact hc.symm

/-- Every common actual terminal correction has the explicit source planar lower radius with a controlled denominator.
Use: obtain a quantitative information lower bound for the genuinely constructed admissible signed scenarios.
Article: main_krylov, thm:C, lower radius βρ/(1+2β).
Proof: the exact true inverse-mean column makes the hidden numerator at
least βρ. The actual inverse mean has norm at most two, so the radius
denominator is at most 1+2β. Apply the existing exact two-scenario theorem
to these actual mean and hidden matrices and the arbitrary common correction.
-/
theorem planar_two_scenario_lower (e f : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0)
    (x β ρ : ℝ) (hx : |x|≤(1/2 : ℝ)) (hβ : 0≤β) (hρ : 0≤ρ)
    (u : EuclideanSpace ℝ (Fin n)) :
    let M := 1+planarMatrix e f 0 x 0
    let Δ := planarMatrix e f β 0 0
    β*ρ/(1+2*β)≤max ‖ρ • e+cgOperator (M+Δ) u‖ ‖ρ • e+cgOperator (M-Δ) u‖ := by
  -- Every matrix in the information bound is the actual physical planar matrix.
  let M := 1+planarMatrix e f 0 x 0
  let Δ := planarMatrix e f β 0 0
  let K := cgOperator (Δ*M⁻¹)
  have hx₁ : |x|<1 := hx.trans_lt (by norm_num)
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (terminal_cross_posDef e f he hf hef hx₁).det_pos.ne'
  have hfe : inner ℝ f e=0 := (real_inner_comm e f).trans hef
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hDe : cgOperator Δ e=β • e := by
    simp only [Δ,cgOperator,planarMatrix_action,hee,hfe,mul_one,mul_zero,zero_smul,add_zero]
  have hDf : cgOperator Δ f=0 := by
    simp only [Δ,cgOperator,planarMatrix_action,hef,mul_zero,zero_mul,zero_smul,add_zero]
  have hden : 0<1-x^2 := by nlinarith [sq_abs x,abs_nonneg x]
  have hnum : K (ρ • e)=(β*ρ/(1-x^2)) • e := by
    change cgOperator (Δ*M⁻¹) (ρ • e)=_
    simp only [cgOperator,map_mul,mul_apply_eq_comp]
    change cgOperator Δ (cgOperator M⁻¹ (ρ • e))=_
    rw [map_smul,planar_cross_inverse_e e f he hf hef x hx₁,map_smul,map_smul,
      map_sub,map_smul,hDe,hDf,smul_zero,sub_zero,smul_smul,smul_smul]
    congr 1
    ring
  have hn : β*ρ≤‖K (ρ • e)‖ := by
    rw [hnum,norm_smul,he,mul_one,Real.norm_of_nonneg (div_nonneg (mul_nonneg hβ hρ) hden.le)]
    apply (le_div_iff₀ hden).mpr
    exact mul_le_of_le_one_right (mul_nonneg hβ hρ) (by nlinarith [sq_nonneg x])
  have hJi : ‖cgOperator M⁻¹‖≤2 := by
    apply inverse_operator_norm_le_two (cgOperator M)
    · simp only [cgOperator,← map_mul,mul_nonsing_inv _ hu,map_one]
    · have hs : cgOperator M-1=cgOperator (planarMatrix e f 0 x 0) := by
        simp only [M,cgOperator,map_add,map_one]
        abel
      rw [hs,cgOperator,Matrix.l2_opNorm_toEuclideanCLM]
      exact (planar_cross_norm_le e f he hf hef x).trans hx
  have hK : ‖K‖≤2*β := by
    have hD : ‖cgOperator Δ‖=β := by
      rw [cgOperator,Matrix.l2_opNorm_toEuclideanCLM,planar_diagonal_norm e f he,abs_of_nonneg hβ]
    calc
      ‖K‖ ≤ ‖cgOperator Δ‖*‖cgOperator M⁻¹‖ := by
        change ‖cgOperator (Δ*M⁻¹)‖≤_
        rw [cgOperator,map_mul]
        exact norm_mul_le _ _
      _ ≤ β*2 := mul_le_mul hD.le hJi (norm_nonneg _) hβ
      _ = 2*β := mul_comm _ _
  have hdpos : 0<Real.sqrt (1+‖K‖^2) := Real.sqrt_pos.mpr (by positivity)
  have hd : Real.sqrt (1+‖K‖^2)≤1+2*β := by
    have hsq : Real.sqrt (1+‖K‖^2)≤1+‖K‖ := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (by positivity)]
      nlinarith [norm_nonneg K]
    exact hsq.trans (add_le_add le_rfl hK)
  have hrad : β*ρ/(1+2*β)≤‖K (ρ • e)‖/Real.sqrt (1+‖K‖^2) := by
    apply (le_div_iff₀ hdpos).mpr
    have hs := mul_le_mul_of_nonneg_left hd (div_nonneg (mul_nonneg hβ hρ) (by positivity : 0≤1+2*β))
    exact (hs.trans_eq (div_mul_cancel₀ _ (by positivity : (1+2*β)≠0))).trans hn
  exact hrad.trans (terminal_two_scenario_lower M Δ hu (ρ • e) u)

/-- The explicit maximizing planar radius differs from the sharp source constant by a uniform cubic budget term.
Use: pass from the exact admissible radius to an all-profile second-order lower estimate, including zero total budget.
Article: main_krylov, thm:C, t²K divided by the true radius denominator is K+O((W+w)³).
Proof: the maximizing coordinates lie on the nonnegative unit circle.
Their hidden diagonal is at most W+w; the actual slack denominator gives
at least a factor 1−4(W+w). The proved bound K≤(W+w)² makes the resulting
loss at most 4(W+w)³, uniformly over every budget profile.
-/
theorem maximizing_planar_radius_lower {W w : ℝ} (hW : 0≤W) (hw : 0≤w)
    (hs : W+w≤(1/2 : ℝ)) {c : ℝ} (hc : 0≤c) :
    let a := maximizingCross W w
    let γ := maximizingComplement W w
    let t := 1-W
    let β := t*(γ*W+w)
    c*(sharpConstant W w-4*(W+w)^3)≤β*(t*a*W*c)/(1+2*β) := by
  -- Bound the true slack and denominator before multiplying the sharp coefficient.
  let a := maximizingCross W w
  let γ := maximizingComplement W w
  let t := 1-W
  let β := t*(γ*W+w)
  let s := W+w
  obtain ⟨hγ,ha,hcircle⟩ := maximizing_coordinates hW hw
  have hγ₁ : γ≤1 := by nlinarith [sq_nonneg a]
  have ht : 0≤t := by dsimp only [t]; linarith
  have ht₁ : t≤1 := by dsimp only [t]; linarith
  have hβ : 0≤β := mul_nonneg ht (add_nonneg (mul_nonneg hγ hW) hw)
  have hβs : β≤s := by
    have hinner : γ*W+w≤s := add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hγ₁ hW) le_rfl
    exact (mul_le_mul_of_nonneg_right ht₁ (add_nonneg (mul_nonneg hγ hW) hw)).trans
      (by simpa only [one_mul] using hinner)
  have hden : 0<1+2*β := by positivity
  have hs₀ : 0≤s := add_nonneg hW hw
  have hWs : W≤s := by dsimp only [s]; linarith
  have hfactor : 1-4*s≤t^2/(1+2*β) := by
    apply (le_div_iff₀ hden).mpr
    dsimp only [t]
    nlinarith [mul_nonneg hs₀ hβ,sq_nonneg W]
  have hK₀ : 0≤sharpConstant W w := sharpConstant_nonneg hW hw
  have hKs : sharpConstant W w≤s^2 :=
    (sharpConstant_upper hW hw).trans (by dsimp only [s]; nlinarith [sq_nonneg W,sq_nonneg w])
  have hsmall : sharpConstant W w-4*s^3≤sharpConstant W w*(1-4*s) := by
    nlinarith [mul_le_mul_of_nonneg_left hKs (by positivity : 0≤4*s)]
  have hnum : β*(t*a*W*c)=c*t^2*sharpConstant W w := by
    dsimp only [β,a,γ,sharpConstant]
    ring
  calc
    c*(sharpConstant W w-4*s^3) ≤ c*(sharpConstant W w*(1-4*s)) := mul_le_mul_of_nonneg_left hsmall hc
    _ = (c*sharpConstant W w)*(1-4*s) := by ring
    _ ≤ (c*sharpConstant W w)*(t^2/(1+2*β)) := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hc hK₀)
    _ = β*(t*a*W*c)/(1+2*β) := by rw [hnum]; ring


end
end krylov.Information
