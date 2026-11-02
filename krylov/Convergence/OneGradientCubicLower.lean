import krylov.Convergence.OneGradientCubicMetric
import krylov.Convergence.OneGradientClippedMagnitude

/-!
Article: main_krylov, thm:LB, genuine arbitrary-policy cubic lower bound.
Use: combine actual nonlinear oracle indistinguishability, original
last-query clipping and the output-independent metric inequality. The
result applies to every original span-restricted one-gradient method.
Source: the complete opposite-cubic argument in Appendix G; no assumption
about the method's output or its own step independence is added.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Every original span-restricted one-gradient policy has two genuine
clipped rank-one cubic sources with identical real transcripts and
outputs. At least one true output gradient obeys the sharp endpoint
lower target with an explicit uniform perturbation denominator. The
latter depends on the fibre width and starting scale, and not on the
possibly arbitrarily large final query or output. Article: thm:LB. -/
theorem oneGradientCubic_clipped_actual_lower
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g a x₀ : E) (N : ℕ)
    (ha : ∀ x∈CG.krylovSpace (cgOperator base) g N,inner ℝ a x=0)
    (hx₀ : g+cgOperator base x₀=0)
    (M δ ρ : ℝ) (hM : 0<M) (hδ : 0≤δ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hy : |inner ℝ a x₀|≤δ/M)
    (hsep : ρ*|inner ℝ a x₀|≤|inner ℝ a x₀-inner ℝ a (oneGradientLastQuery m (cgOperator base) g N)|) :
    let p := inner ℝ a (oneGradientLastQuery m (cgOperator base) g N)
    let Mp := oneGradientClippedMagnitude M δ p
    let Gp := oneGradientCubicFibreGradient (cgOperator base) g a (-Mp*p/2) Mp
    let Gm := oneGradientCubicFibreGradient (cgOperator base) g a (Mp*p/2) (-Mp)
    let R := cgOperator (metricRoot base)⁻¹
    let c := ‖R a‖
    let y₀ := inner ℝ a x₀
    let B := c^2*(M*|y₀|+δ)+M*c^4/4*|y₀| *(M*|y₀|+2*δ)
    |Mp*p/2|≤δ ∧
    oneGradientFunctionRun m Gp 0 (N+1)=oneGradientFunctionRun m Gm 0 (N+1) ∧
    oneGradientFunctionOutput m Gp 0 (N+1)=oneGradientFunctionOutput m Gm 0 (N+1) ∧
    ((M/2*c)*ρ*|y₀|^2)/(1+B)≤max
      ‖R (Gp (oneGradientFunctionOutput m Gp 0 (N+1)))‖
      ‖R (Gm (oneGradientFunctionOutput m Gm 0 (N+1)))‖ := by
  let p := inner ℝ a (oneGradientLastQuery m (cgOperator base) g N)
  let Mp := oneGradientClippedMagnitude M δ p
  let Gp := oneGradientCubicFibreGradient (cgOperator base) g a (-Mp*p/2) Mp
  let Gm := oneGradientCubicFibreGradient (cgOperator base) g a (Mp*p/2) (-Mp)
  let R := cgOperator (metricRoot base)⁻¹
  let c := ‖R a‖
  let y₀ := inner ℝ a x₀
  let B := c^2*(M*|y₀|+δ)+M*c^4/4*|y₀| *(M*|y₀|+2*δ)
  let out := m.outputDisplacement (oneGradientRun m (fun _=>cgOperator base) g (N+1))
  have hbnd := oneGradientClippedMagnitude_bounds M δ p hM.le hδ
  have hMp : 0≤Mp := hbnd.1
  have hp : oneGradientFunctionRun m Gp 0 (N+1)=oneGradientRun m (fun _=>cgOperator base) g (N+1) := by
    simpa only [Gp,Mp,p,neg_mul,one_mul] using oneGradientCubicTwins_history m hm (cgOperator base) g a Mp N ha 1
  have hm' : oneGradientFunctionRun m Gm 0 (N+1)=oneGradientRun m (fun _=>cgOperator base) g (N+1) := by
    simpa only [Gm,Mp,p,neg_mul,one_mul,neg_neg] using oneGradientCubicTwins_history m hm (cgOperator base) g a Mp N ha (-1)
  have hop : oneGradientFunctionOutput m Gp 0 (N+1)=out := by
    unfold oneGradientFunctionOutput oneGradientFunctionPoint
    rw [hp,zero_add]
    rfl
  have hom : oneGradientFunctionOutput m Gm 0 (N+1)=out := by
    unfold oneGradientFunctionOutput oneGradientFunctionPoint
    rw [hm',zero_add]
    rfl
  have hcurv : |Mp*p/2|≤δ := by
    rw [abs_div,abs_mul,abs_of_nonneg hbnd.1,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by nlinarith only [hbnd.2.2])
  refine ⟨hcurv,hp.trans hm'.symm,hop.trans hom.symm,?_⟩
  change _≤max ‖R (Gp (oneGradientFunctionOutput m Gp 0 (N+1)))‖
    ‖R (Gm (oneGradientFunctionOutput m Gm 0 (N+1)))‖
  rw [hop,hom]
  have hl := oneGradientCubicTwins_metric_output_lower base hb g a x₀ out hx₀ Mp p hbnd.1
  let T := (Mp/2*c)*|y₀| *|y₀-p|
  let η := (Mp/2*c)*c*(|y₀|+|y₀-p|+c*T)
  change T/(1+η)≤max ‖R (Gp out)‖ ‖R (Gm out)‖ at hl
  have hT : (M/2*c)*ρ*|y₀|^2≤T := by
    have hh := mul_le_mul_of_nonneg_left
      (oneGradientClippedMagnitude_lower M δ p y₀ ρ hM hδ hρ hρ1 hy hsep) (by positivity : 0≤c/2)
    dsimp only [T]
    nlinarith only [hh]
  have hη : η≤B := oneGradientClippedMagnitude_relative_error M δ p y₀ c hM.le hδ (norm_nonneg _)
  have hη0 : 0≤η := by dsimp only [η,T,c];positivity
  have hB0 : 0≤B := hη0.trans hη
  have hT0 : 0≤T := by dsimp only [T];positivity
  exact ((div_le_div_of_nonneg_left hT0 (by linarith only [hη0] : 0<1+η)
    (by linarith only [hη] : 1+η≤1+B)).trans'
      (div_le_div_of_nonneg_right hT (by linarith only [hB0] : 0≤1+B))).trans hl

end
end krylov.Convergence
