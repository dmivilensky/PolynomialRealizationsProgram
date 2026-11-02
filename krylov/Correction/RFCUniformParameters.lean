import krylov.Correction.RFCUniformConstants
import krylov.Correction.GatedPrefixGrowth

/-!
Article: main_krylov, thm:UCq, uniform nonstagnation allowances.
Use: Select actual finite RFC induction constants and a positive source radius
before every reference, spectral scale, measured operator sequence and run.
Source: proved finite coefficient signs, the actual recording radius and
a finite minimum of elementary positive scalar allowances.
-/

namespace krylov.Correction
noncomputable section
open krylov.Stability

/-- Dimension, condition ratio and gate threshold alone determine common positive nonstagnation constants and a radius satisfying every genuine RFC prefix allowance.
Use: Remove all numerical-smallness hypotheses from the actual finite nonstagnating-prefix theorem.
Article: main_krylov, thm:UCq.
Proof: Use the proved actual growth and projected-residual coefficients to construct the residual allowance. The finite observed-search recurrence supplies the step constant. Choose the nonstagnation threshold above both true gradient and step allowances, and intersect the real recording radius with explicit angle, residual and projected-conjugacy radii.
-/
theorem rfc_uniform_prefix_parameters (N : ℕ) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ K C L M₀ ε₀ : ℝ, K=2*gatedCorrectionConstant N γ ∧ 0<C ∧ 0≤L ∧ 0<M₀ ∧ 0<ε₀ ∧
      (gatedGrowthConstant N γ)^N≤L ∧
      4*gatedProjectedConstant N K*(Real.sqrt N*(2+K))*L≤C ∧
      (N : ℝ)*(rfcUniformStepConstant N κ K C L N+(1+K)*(rfcUniformStepConstant N κ K C L N+1))+4*κ*C<M₀ ∧
      Real.sqrt κ*(rfcUniformStepConstant N κ K C L N+2)≤M₀ ∧
      ∀ ε : ℝ, 0≤ε → ε≤ε₀ → ε≤1/2 ∧
        ((1+K)*ε≤1/2 ∧ (N : ℝ)*((1+K)*ε)≤γ/4 ∧ (N : ℝ)*((1+K)*ε)≤1) ∧
        (N : ℝ)*(rfcLinearAngleConstant N K C*ε)≤(1-γ)/8 ∧
        gatedProjectedConstant N K*ε≤1/2 ∧ 4*Real.sqrt N*((1+K)*ε)≤1/2 := by
  let K := 2*gatedCorrectionConstant N γ
  let F := gatedProjectedConstant N K
  let H := Real.sqrt N*(2+K)
  let L := (gatedGrowthConstant N γ)^N
  let C := 4*F*H*L+1
  have hK : 0≤K := by dsimp only [K]; exact mul_nonneg (by norm_num) (gatedCorrectionConstant_nonneg N γ)
  have hF : 0≤F := gatedProjectedConstant_nonneg N hK
  have hH : 0≤H := by dsimp only [H]; positivity
  have hL : 0≤L := by
    have hg : 0≤gatedGrowthConstant N γ := by unfold gatedGrowthConstant; positivity
    exact pow_nonneg hg N
  have hC : 0<C := by dsimp only [C]; positivity
  have hκ0 : 0≤κ := by linarith
  let S := rfcUniformStepConstant N κ K C L N
  have hS : 0≤S := rfcUniformStepConstant_nonneg N hκ0 hK hC.le hL N
  let D := (N : ℝ)*(S+(1+K)*(S+1))
  have hD : 0≤D := by dsimp only [D]; positivity
  let M := D+4*κ*C+Real.sqrt κ*(S+2)+1
  have hM : 0<M := by dsimp only [M]; positivity
  let a := rfcLinearAngleConstant N K C
  have ha : 0<a := rfcLinearAngleConstant_pos N hK hC.le
  obtain ⟨r,hr,hrecord⟩ := gated_recording_radius N γ hγ
  let rA := (1-γ)/(8*((N : ℝ)*a+1))
  let rF := 1/(2*(F+1))
  let rP := 1/(8*(Real.sqrt N*(1+K)+1))
  let δ := min r (min (1/2) (min rA (min rF rP)))
  have hδ : 0<δ := lt_min hr (lt_min (by norm_num)
    (lt_min (div_pos (by linarith) (by positivity)) (lt_min (by positivity) (by positivity))))
  refine ⟨K,C,L,M,δ,rfl,hC,hL,hM,hδ,le_rfl,?_,?_,?_,?_⟩
  · change 4*F*H*L≤4*F*H*L+1; linarith
  · change D+4*κ*C<D+4*κ*C+Real.sqrt κ*(S+2)+1
    have hs : 0≤Real.sqrt κ*(S+2) := mul_nonneg (Real.sqrt_nonneg κ) (by linarith)
    linarith
  · change Real.sqrt κ*(S+2)≤D+4*κ*C+Real.sqrt κ*(S+2)+1
    have ht : 0≤4*κ*C := by positivity
    linarith
  · intro ε hε he
    have her := he.trans (min_le_left _ _)
    have hehalf := he.trans ((min_le_right _ _).trans (min_le_left _ _))
    have heA := he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have heF := he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have heP := he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have hA' : ε*(8*((N : ℝ)*a+1))≤1-γ := (le_div_iff₀ (by positivity : 0<8*((N : ℝ)*a+1))).mp heA
    have hF' : ε*(2*(F+1))≤1 := (le_div_iff₀ (by positivity : 0<2*(F+1))).mp heF
    have hP' : ε*(8*(Real.sqrt N*(1+K)+1))≤1 :=
      (le_div_iff₀ (by positivity : 0<8*(Real.sqrt N*(1+K)+1))).mp heP
    refine ⟨hehalf,?_,?_,?_,?_⟩
    · simpa only [K] using hrecord ε hε her
    · change (N : ℝ)*(a*ε)≤(1-γ)/8; nlinarith only [hA',hε]
    · change F*ε≤1/2; nlinarith only [hF',hε]
    · nlinarith only [hP',hε]

end
end krylov.Correction
