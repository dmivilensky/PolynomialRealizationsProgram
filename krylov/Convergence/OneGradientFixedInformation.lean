import krylov.Convergence.OneGradientNormalGeometry
import krylov.Nonlinear.ReferenceCycleScale

/-!
Article: main_krylov, thm:LB, literal fixed normalized information.
Use: keep the original hidden unit axis and two actual positive endpoint
matrices fixed while the forcing h*g tends to zero. Actual histories,
reference errors, last lengths and endpoint selection are derived from
the original known operator restriction for every M1 policy.
Source: true Krylov information, genuine CG nonstagnation/termination
and exact initial-gradient homogeneity, with no policy continuity premise.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Genuine full reference support survives every nonzero forcing scale.
Article: main_krylov, thm:LB, fixed normalized information. -/
theorem oneGradient_full_count_smul
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E)
    (hfull : referenceAtomCount A hA g=k+1) (h : ℝ) (hh : h≠0) :
    referenceAtomCount A hA (h • g)=k+1 := by
  have hnon : CG.gradient (cgOperator A) (h • g) k≠0 := by
    rw [reference_gradient_smul (cgOperator A) (cgOperator_positive A hA).1
      (cgOperator_positive A hA).2 g h hh k]
    exact smul_ne_zero hh (cg_nonstagnation A hA g k (by rw [hfull];omega))
  have hlo : k<referenceAtomCount A hA (h • g) := by
    by_contra hc
    exact hnon ((cg_stopping_iff A hA (h • g) k).mpr (by omega))
  have hhi : referenceAtomCount A hA (h • g)≤k+1 := by
    unfold referenceAtomCount activeSpectralValues
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _))
  omega

/-- Every true positive information completion has the actual full atom
count, without assuming its own query or independence properties.
Article: main_krylov, thm:LB. -/
theorem oneGradient_information_full_count
    (A C : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (hC : C.PosDef) (g : E)
    (hfull : referenceAtomCount A hA g=k+1)
    (hact : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C v=cgOperator A v) :
    referenceAtomCount C hC g=k+1 := by
  have hs := cg_information_prefix (cgOperator A) (cgOperator C) (cgOperator_positive A hA).1
    (cgOperator_positive A hA).2 g
    (fun j hj=>cg_nonstagnation A hA g j (by rw [hfull];omega)) hact k le_rfl
  have hnon : CG.gradient (cgOperator C) g k≠0 := by
    rw [show CG.gradient (cgOperator C) g k=CG.gradient (cgOperator A) g k from congrArg CGState.gradient hs]
    exact cg_nonstagnation A hA g k (by rw [hfull];omega)
  have hlo : k<referenceAtomCount C hC g := by
    by_contra hc
    exact hnon ((cg_stopping_iff C hC g k).mpr (by omega))
  have hhi : referenceAtomCount C hC g≤k+1 := by
    unfold referenceAtomCount activeSpectralValues
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _))
  omega

/-- The fixed known action is the true known action at every nonzero
forcing scale. Article: main_krylov, thm:LB. -/
theorem oneGradient_information_smul
    (A C : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (g : E) (h : ℝ) (hh : h≠0)
    (hact : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C v=cgOperator A v) :
    ∀ v∈CG.krylovSpace (cgOperator A) (h • g) k,cgOperator C v=cgOperator A v := by
  rw [oneGradient_krylovSpace_smul _ _ _ hh]
  exact hact

/-- Every fixed unit hidden axis remains the real old-information normal
on every actual completion and forcing scale. Article: thm:LB. -/
theorem oneGradient_fixed_hidden_flag
    (A C : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (g a : E) (h : ℝ) (hh : h≠0)
    (hact : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C v=cgOperator A v)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0) :
    ∀ v,v∈CG.krylovSpace (cgOperator C) (h • g) k ↔ inner ℝ a v=0 := by
  rw [oneGradient_krylovSpace_smul _ _ _ hh,
    information_krylov_space (cgOperator A) (cgOperator C) g k hact k (by omega)]
  exact hflag

/-- The actual minimizer coordinate on a fixed information completion
is minus the true last CG length times the common reference residual
coordinate, uniformly in every positive forcing scale. Article: thm:LB. -/
theorem oneGradient_fixed_minimizer_coordinate
    (A C : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (hC : C.PosDef) (g a : E) (ha : ‖a‖=1)
    (hfull : referenceAtomCount A hA g=k+1)
    (hact : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C v=cgOperator A v)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0)
    (h : ℝ) (hh : 0<h) :
    inner ℝ a (oneGradientQuadraticMinimizer C (h • g))=
      (-h*inner ℝ a (CG.gradient (cgOperator A) g k))*CG.length (cgOperator C) g k := by
  have hCfull := oneGradient_information_full_count A C hA hC g hfull hact
  have hscaled := oneGradient_full_count_smul C hC g hCfull h hh.ne'
  have hflagC := oneGradient_fixed_hidden_flag A C g a h hh.ne' hact hflag
  rw [oneGradient_normal_minimizer_coordinate C hC (h • g) a ha hscaled hflagC,
    reference_length_smul (cgOperator C) (cgOperator_positive C hC).1 (cgOperator_positive C hC).2 g h hh.ne' k,
    reference_gradient_smul (cgOperator C) (cgOperator_positive C hC).1 (cgOperator_positive C hC).2 g h hh.ne' k]
  have hs := cg_information_prefix (cgOperator A) (cgOperator C) (cgOperator_positive A hA).1
    (cgOperator_positive A hA).2 g
    (fun j hj=>cg_nonstagnation A hA g j (by rw [hfull];omega)) hact k le_rfl
  rw [show CG.gradient (cgOperator C) g k=CG.gradient (cgOperator A) g k from congrArg CGState.gradient hs,
    inner_smul_right]
  ring

/-- Original fixed normalized information forces the sharp endpoint
separation at every positive scale, for arbitrary data-only M1 policies.
The endpoint matrices and minimax coefficient are fixed before choosing
the scale or policy; no method regularity is imposed. Article: thm:LB. -/
theorem oneGradient_fixed_endpoint_selection
    (A C₀ C₁ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (hC₀ : C₀.PosDef) (hC₁ : C₁.PosDef)
    (g a : E) (ha : ‖a‖=1) (hfull : referenceAtomCount A hA g=k+1)
    (hact₀ : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C₀ v=cgOperator A v)
    (hact₁ : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C₁ v=cgOperator A v)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0)
    (horder : CG.length (cgOperator C₀) g k≤CG.length (cgOperator C₁) g k)
    (method : OneGradientMethod E) (hmeth : OneGradientSpanRestricted method) (h : ℝ) (hh : 0<h) :
    let ρ:=intervalMinimaxValue (CG.length (cgOperator C₀) g k) (CG.length (cgOperator C₁) g k)
    ∃ C∈({C₀,C₁} : Set (Matrix (Fin (k+1)) (Fin (k+1)) ℝ)), ∃ _hC : C.PosDef,
      ρ*|inner ℝ a (oneGradientQuadraticMinimizer C (h • g))|≤
        |inner ℝ a (oneGradientQuadraticMinimizer C (h • g))-
          inner ℝ a (oneGradientLastQuery method (cgOperator C) (h • g) k)| := by
  have hα₀ := cgLength_pos C₀ hC₀ g k (by rw [oneGradient_information_full_count A C₀ hA hC₀ g hfull hact₀];omega)
  let γ := -h*inner ℝ a (CG.gradient (cgOperator A) g k)
  let p := inner ℝ a (oneGradientLastQuery method (cgOperator A) (h • g) k)
  obtain ⟨α,hα,hsep⟩ := oneGradient_endpoint_coordinate_obstruction
    (CG.length (cgOperator C₀) g k) (CG.length (cgOperator C₁) g k) γ p hα₀ horder
  have hy (C : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hC : C.PosDef)
      (hact : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C v=cgOperator A v) :
      inner ℝ a (oneGradientQuadraticMinimizer C (h • g))=γ*CG.length (cgOperator C) g k :=
    oneGradient_fixed_minimizer_coordinate A C hA hC g a ha hfull hact hflag h hh
  have hp (C : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
      (hact : ∀ v∈CG.krylovSpace (cgOperator A) g k,cgOperator C v=cgOperator A v) :
      inner ℝ a (oneGradientLastQuery method (cgOperator C) (h • g) k)=p := by
    rw [oneGradientLastQuery_information method hmeth (cgOperator A) (cgOperator C) (h • g) k
      (oneGradient_information_smul A C g h hh.ne' hact)]
  rcases hα with hα|hα
  · refine ⟨C₀,by simp,hC₀,?_⟩
    rw [hy C₀ hC₀ hact₀,hp C₀ hact₀]
    rw [hα] at hsep
    exact hsep.trans_eq (abs_sub_comm _ _)
  · rw [mem_singleton_iff] at hα
    refine ⟨C₁,by simp,hC₁,?_⟩
    rw [hy C₁ hC₁ hact₁,hp C₁ hact₁]
    rw [hα] at hsep
    exact hsep.trans_eq (abs_sub_comm _ _)

end
end krylov.Convergence
