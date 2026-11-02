import krylov.Functions.NormalizedReferenceCompact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: main_krylov, s7:N, genuine physical compactness from normalized pairs.
Use: derive all scalar normalization bounds from an actual first-query drift
and the positive minimizer Hessian. No frozen full-reference assumption is
needed. Source: finite-dimensional injective lower bound and true norm estimates.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- A positive true finite-dimensional Hessian has a uniform positive lower
bound on unit starts. Article: main_krylov, s7:N, normalization scales. -/
theorem positiveOperator_unit_lower (Q : E →L[ℝ] E)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) :
    0<‖Q‖ ∧ ∃ m : ℝ, 0<m ∧ ∀ u : E, ‖u‖=1 → m≤‖Q u‖ := by
  have hinj : Function.Injective Q.toLinearMap := by
    intro x y hxy
    change Q x=Q y at hxy
    have hz : Q (x-y)=0 := by rw [map_sub,hxy,sub_self]
    by_contra hne
    have hp := hpos (x-y) (sub_ne_zero.mpr hne)
    rw [hz,inner_zero_right] at hp
    exact (lt_irrefl 0 hp)
  obtain ⟨D,hD,hanti⟩ := Q.toLinearMap.injective_iff_antilipschitz.mp hinj
  have hDr : 0<(D : ℝ) := hD
  have hQ : Q≠0 := by
    intro hz
    obtain ⟨v,hv⟩ := exists_ne (0:E)
    have hp := hpos v hv
    simp only [hz,_root_.zero_apply,inner_zero_right] at hp
    exact (lt_irrefl 0 hp)
  refine ⟨norm_pos_iff.mpr hQ,1/(D:ℝ),by positivity,?_⟩
  intro u hu
  have hb := Q.bound_of_antilipschitz hanti u
  rw [hu] at hb
  exact (div_le_iff₀ hDr).mpr (by nlinarith only [hb])

/-- Literal normalized-reference compactness plus the genuine first-query
source drift yields a true compact positive full physical-reference set.
All scale intervals are derived, uniformly for unit starts. Article: s7:N. -/
theorem normalized_reference_source_compact (Q : E →L[ℝ] E)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (A : ℝ → E → E →L[ℝ] E) (g : ℝ → E → E)
    (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0)
    (hsource : ∃ es C : ℝ, 0<es ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<es →
      ∀ u : E, ‖u‖=1 → ‖(A ε u-Q,g ε u-Q u)‖≤C*ε) :
    ∃ ep : ℝ, 0<ep ∧ ∃ P : Set ((E →L[ℝ] E) × E), IsCompact P ∧
      (∀ z∈P, z.1.toLinearMap.IsSymmetric ∧
        (∀ v : E, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0) ∧
      ∀ ε : ℝ, 0<ε → ε<ep → ∀ u : E, ‖u‖=1 →
        normalizedReference (A ε u) (g ε u)∈K → (A ε u,g ε u)∈P := by
  obtain ⟨hQ,m,hm,hmin⟩ := positiveOperator_unit_lower Q hpos
  obtain ⟨es,C,hes,hC,hsource⟩ := hsource
  let ep := min es (min (‖Q‖/(2*(C+1))) (min (m/(2*(C+1))) (1/(C+1))))
  have hep : 0<ep := by dsimp only [ep]; positivity
  let P := scaledReferenceCompact K (‖Q‖/2) (‖Q‖+1) (m/2) (‖Q‖+1)
  refine ⟨ep,hep,P,scaledReferenceCompact_isCompact K hK _ _ _ _,
    scaledReferenceCompact_nondegenerate K N hquad _ _ _ _ (by positivity) (by positivity),?_⟩
  intro ε hε he u hu hKu
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  have hA := (norm_fst_le (A ε u-Q,g ε u-Q u)).trans hs
  have hg := (norm_snd_le (A ε u-Q,g ε u-Q u)).trans hs
  have hsmallA : C*ε≤‖Q‖/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(C+1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [hh,hε]
  have hsmallg : C*ε≤m/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(C+1))).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    nlinarith only [hh,hε]
  have hsmall : C*ε≤1 := by
    have hh := (lt_div_iff₀ (by positivity : 0<C+1)).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    nlinarith only [hh,hε]
  have hQu : ‖Q u‖≤‖Q‖ := by simpa only [hu,mul_one] using Q.le_opNorm u
  apply mem_scaledReferenceCompact K _ _ _ _ _ _ hKu
  · constructor
    · have hh := norm_sub_norm_le Q (A ε u)
      rw [norm_sub_rev] at hh
      linarith only [hh,hA,hsmallA]
    · have hh := norm_sub_norm_le (A ε u) Q
      linarith only [hh,hA,hsmall]
  · constructor
    · have hh := norm_sub_norm_le (Q u) (g ε u)
      rw [norm_sub_rev] at hh
      have hl := hmin u hu
      linarith only [hh,hg,hsmallg,hl]
    · have hh := norm_sub_norm_le (g ε u) (Q u)
      linarith only [hh,hg,hsmall,hQu]

end
end krylov.Functions
