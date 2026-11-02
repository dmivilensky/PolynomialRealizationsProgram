import krylov.Convergence.OneGradientSourceWitness

/-!
Article: main_krylov, thm:LB, fixed realizable Krylov information.
Use: quantify over arbitrary original one-gradient policies and derive the
adversarial endpoint from their genuine common observations. Sources have
true local minima, true positive Hessians, the true canonical tensor
budget and the true-Hessian reference CG error in the lower bound.
Source: the proved actual two-completion information theorem followed by
the uniform genuine clipped-cubic source construction.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The genuine fixed-information endpoint pair forces a true scalar
cubic lower bound at every sufficiently small starting scale. Endpoints,
constants, and the admissible scale are fixed before the arbitrary method.
Article: main_krylov, thm:LB, fixed-information assertion. -/
theorem oneGradient_fixed_fibre_true_lower
    (A C₀ C₁ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (hC₀ : C₀.PosDef) (hC₁ : C₁.PosDef)
    (g a : E) (ha : ‖a‖=1) (hfull : referenceAtomCount A hA g=k+1)
    (hact₀ : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C₀ v=cgOperator A v)
    (hact₁ : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C₁ v=cgOperator A v)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0)
    (horder : CG.length (cgOperator C₀) g k≤CG.length (cgOperator C₁) g k)
    (Mhat m η : ℝ) (hMhat : 0<Mhat) (hm : 0<m) (hη : 0<η) (hη1 : η<1)
    (hbase₀ : ∀ v,m*‖v‖^2≤ inner ℝ v (cgOperator C₀ v))
    (hbase₁ : ∀ v,m*‖v‖^2≤ inner ℝ v (cgOperator C₁ v)) :
    let ρ:=intervalMinimaxValue (CG.length (cgOperator C₀) g k) (CG.length (cgOperator C₁) g k)
    ∃ s : ℝ,0<s ∧∀ h : ℝ,0<h → h<s →∀ method : OneGradientMethod E,
      OneGradientSpanRestricted method →
      ∃ C∈({C₀,C₁} : Set (Matrix (Fin (k+1)) (Fin (k+1)) ℝ)), ∃ R : ℝ,0<R ∧
        ∃ w : OneGradientCubicLowerWitness method C (h • g) a R ((1+η)^3*Mhat)
          ((1-η)/(1+η)^2*(Mhat/2)*ρ),
          ‖oneGradientCubicTrueHessian C a w.curvature w.cubic w.minimizer-C‖≤η*m := by
  let ρ:=intervalMinimaxValue (CG.length (cgOperator C₀) g k) (CG.length (cgOperator C₁) g k)
  have hfull₀ := oneGradient_information_full_count A C₀ hA hC₀ g hfull hact₀
  have hfull₁ := oneGradient_information_full_count A C₁ hA hC₁ g hfull hact₁
  have hα₀ := cgLength_pos C₀ hC₀ g k (by rw [hfull₀];omega)
  have hα₁ := cgLength_pos C₁ hC₁ g k (by rw [hfull₁];omega)
  have hρ : 0≤ρ := by
    dsimp only [ρ,intervalMinimaxValue]
    exact div_nonneg (sub_nonneg.mpr horder) (by linarith)
  have hρ1 : ρ≤1 := by
    dsimp only [ρ,intervalMinimaxValue]
    apply (div_le_one (by linarith : 0<CG.length (cgOperator C₁) g k+CG.length (cgOperator C₀) g k)).mpr
    linarith only [hα₀]
  have hflag₀ := oneGradient_fixed_hidden_flag A C₀ g a 1 one_ne_zero hact₀ hflag
  have hflag₁ := oneGradient_fixed_hidden_flag A C₁ g a 1 one_ne_zero hact₁ hflag
  simp only [one_smul] at hflag₀ hflag₁
  obtain ⟨R₀,s₀,hR₀,hs₀,hsource₀⟩ := oneGradient_endpoint_small_source_witness C₀ hC₀ g a ha hfull₀ hflag₀
    Mhat m ρ η hMhat hm hρ hρ1 hη hη1 hbase₀
  obtain ⟨R₁,s₁,hR₁,hs₁,hsource₁⟩ := oneGradient_endpoint_small_source_witness C₁ hC₁ g a ha hfull₁ hflag₁
    Mhat m ρ η hMhat hm hρ hρ1 hη hη1 hbase₁
  refine ⟨min s₀ s₁,lt_min hs₀ hs₁,?_⟩
  intro h hh hhsmall method hmeth
  obtain ⟨C,hCmem,hC,hsep⟩ := oneGradient_fixed_endpoint_selection A C₀ C₁ hA hC₀ hC₁ g a ha hfull
    hact₀ hact₁ hflag horder method hmeth h hh
  rcases hCmem with hCeq|hCeq
  · subst C
    obtain ⟨w,hw⟩ := hsource₀ h hh (hhsmall.trans_le (min_le_left _ _)) method hmeth hsep
    exact ⟨C₀,by simp,R₀,hR₀,w,hw⟩
  · rw [mem_singleton_iff] at hCeq
    subst C
    obtain ⟨w,hw⟩ := hsource₁ h hh (hhsmall.trans_le (min_le_right _ _)) method hmeth hsep
    exact ⟨C₁,by simp,R₁,hR₁,w,hw⟩

/-- The elementary loss parameters used to pass from exact metric
normalization factors to the article's single delta. Article: thm:LB. -/
theorem oneGradient_true_lower_loss {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    0<δ/10 ∧δ/10<1 ∧(1+δ/10)^3≤1+δ ∧
      1-δ≤(1-δ/10)/(1+δ/10)^2 := by
  have hη : 0<δ/10 := by positivity
  have hη1 : δ/10<1/10 := by linarith
  refine ⟨hη,by linarith,?_,?_⟩
  · have hsq : (δ/10)^2≤(δ/10)/10 := by nlinarith
    have hcube : (δ/10)^3≤(δ/10)^2/10 := by nlinarith [mul_le_mul_of_nonneg_left hsq hη.le]
    nlinarith only [hsq,hcube]
  · apply (le_div_iff₀ (sq_pos_of_pos (show 0<1+δ/10 by positivity))).mpr
    have hcube : 0≤δ^3 := by positivity
    nlinarith only [hδ,hcube,sq_nonneg δ]

end
end krylov.Convergence
