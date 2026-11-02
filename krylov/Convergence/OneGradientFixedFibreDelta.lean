import krylov.Convergence.OneGradientFixedFibreLower

/-!
Article: main_krylov, thm:LB, printed fixed-information lower bound.
Use: express the genuine adversarial source theorem with the article's
single relative loss delta, including the true spectral interval.
Source: the proved uniform actual-source theorem, the elementary explicit
loss conversion, and true-Hessian spectral perturbation bounds.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- A genuine source certificate permits weakening its stated numerical
budget and lower target without changing the source or its minimizer.
Article: main_krylov, thm:LB. -/
def OneGradientCubicLowerWitness.weaken
    {method : OneGradientMethod E} {A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ}
    {g a : E} {R B₀ B₁ K₀ K₁ : ℝ}
    (w : OneGradientCubicLowerWitness method A g a R B₀ K₀)
    (hB : B₀≤B₁) (hK : K₁≤K₀) : OneGradientCubicLowerWitness method A g a R B₁ K₁ :=
  { w with tensor_budget:=w.tensor_budget.trans hB
           returned_gradient:=(mul_le_mul_of_nonneg_right hK (sq_nonneg _)).trans w.returned_gradient }

/-- Original fixed-information lower bound, in the true source Hessian
metric, with a single prescribed delta. The actual endpoint is selected
from the method's measured common transcript; no separation, source
minimizer, tensor bound, spectral bound or output estimate is presumed.
Article: main_krylov, thm:LB, fixed realizable information assertion. -/
theorem oneGradient_fixed_fibre_delta_true_lower
    (A C₀ C₁ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (hC₀ : C₀.PosDef) (hC₁ : C₁.PosDef)
    (g a : E) (ha : ‖a‖=1) (hfull : referenceAtomCount A hA g=k+1)
    (hact₀ : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C₀ v=cgOperator A v)
    (hact₁ : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C₁ v=cgOperator A v)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0)
    (horder : CG.length (cgOperator C₀) g k≤CG.length (cgOperator C₁) g k)
    (Mhat μ L δ : ℝ) (hMhat : 0<Mhat) (hμ : 0<μ) (hμL : μ≤L) (hδ : 0<δ) (hδ1 : δ<1)
    (hbase₀ : ∀ v,μ*‖v‖^2≤ inner ℝ v (cgOperator C₀ v))
    (hbase₁ : ∀ v,μ*‖v‖^2≤ inner ℝ v (cgOperator C₁ v))
    (hband₀ : ∀ i,μ≤hC₀.1.eigenvalues i ∧hC₀.1.eigenvalues i≤L)
    (hband₁ : ∀ i,μ≤hC₁.1.eigenvalues i ∧hC₁.1.eigenvalues i≤L) :
    let ρ:=intervalMinimaxValue (CG.length (cgOperator C₀) g k) (CG.length (cgOperator C₁) g k)
    ∃ s : ℝ,0<s ∧∀ h : ℝ,0<h → h<s →∀ method : OneGradientMethod E,
      OneGradientSpanRestricted method →
      ∃ C∈({C₀,C₁} : Set (Matrix (Fin (k+1)) (Fin (k+1)) ℝ)), ∃ R : ℝ,0<R ∧
        ∃ w : OneGradientCubicLowerWitness method C (h • g) a R ((1+δ)*Mhat) ((1-δ)*(Mhat/2)*ρ),
          ‖oneGradientCubicTrueHessian C a w.curvature w.cubic w.minimizer-C‖≤δ*μ ∧
          ∀ i,μ*(1-δ)≤w.positive.1.eigenvalues i ∧w.positive.1.eigenvalues i≤L*(1+δ) := by
  obtain ⟨hη,hη1,hbudget,hloss⟩ := oneGradient_true_lower_loss hδ hδ1
  let ρ:=intervalMinimaxValue (CG.length (cgOperator C₀) g k) (CG.length (cgOperator C₁) g k)
  have hα₀ := cgLength_pos C₀ hC₀ g k
    (by rw [oneGradient_information_full_count A C₀ hA hC₀ g hfull hact₀];omega)
  have hα₁ := cgLength_pos C₁ hC₁ g k
    (by rw [oneGradient_information_full_count A C₁ hA hC₁ g hfull hact₁];omega)
  have hρ : 0≤ρ := by
    dsimp only [ρ,intervalMinimaxValue]
    exact div_nonneg (sub_nonneg.mpr horder) (by linarith)
  obtain ⟨s,hs,hsource⟩ := oneGradient_fixed_fibre_true_lower A C₀ C₁ hA hC₀ hC₁ g a ha hfull
    hact₀ hact₁ hflag horder Mhat μ (δ/10) hMhat hμ hη hη1 hbase₀ hbase₁
  refine ⟨s,hs,?_⟩
  intro h hh hhsmall method hmeth
  obtain ⟨C,hCmem,R,hR,w,hw⟩ := hsource h hh hhsmall method hmeth
  have hB : (1+δ/10)^3*Mhat≤(1+δ)*Mhat := mul_le_mul_of_nonneg_right hbudget hMhat.le
  have hK : (1-δ)*(Mhat/2)*ρ≤(1-δ/10)/(1+δ/10)^2*(Mhat/2)*ρ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hloss (by positivity)) hρ
  let w' := w.weaken hB hK
  have hclose : ‖oneGradientCubicTrueHessian C a w'.curvature w'.cubic w'.minimizer-C‖≤δ*μ :=
    hw.trans (mul_le_mul_of_nonneg_right (by linarith : δ/10≤δ) hμ.le)
  refine ⟨C,hCmem,R,hR,w',hclose,?_⟩
  rcases hCmem with hCeq|hCeq
  · subst C
    exact oneGradient_true_metric_spectral_interval C₀ _ hC₀ w'.positive μ L δ hμ hμL hδ.le hband₀ hclose
  · rw [mem_singleton_iff] at hCeq
    subst C
    exact oneGradient_true_metric_spectral_interval C₁ _ hC₁ w'.positive μ L δ hμ hμL hδ.le hband₁ hclose

end
end krylov.Convergence
