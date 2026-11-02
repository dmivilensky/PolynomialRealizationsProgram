import krylov.Reference.PositiveScale
import Mathlib.Analysis.Normed.Module.Normalize

/-!
Article: main_krylov, s7:N, the literal normalized-reference assumption.
Use: recover one genuine compact positive nondegenerate physical-reference
family from the normalized family and positive compact scalar intervals.
Source: true CG scaling and continuous images of compact products.
-/
namespace krylov.Functions
noncomputable section
open Set Metric NormedSpace krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The two original normalized reference coordinates. Article: s7:N. -/
def normalizedReference (A : E →L[ℝ] E) (g : E) : (E →L[ℝ] E) × E :=
  (normalize A,normalize g)

/-- A positive scalar change of the actual gradient does not change the
literal normalized reference. Article: main_krylov, s7:N. -/
theorem normalizedReference_gradient_smul (A : E →L[ℝ] E) (g : E)
    (c : ℝ) (hc : 0<c) : normalizedReference A (c • g)=normalizedReference A g := by
  simp only [normalizedReference,normalize_smul_of_pos hc]

/-- The positive compact lift of a normalized reference family.
Article: main_krylov, s7:N. -/
def scaledReferenceCompact (K : Set ((E →L[ℝ] E) × E)) (a₀ a₁ b₀ b₁ : ℝ) :
    Set ((E →L[ℝ] E) × E) :=
  (fun z : ((E →L[ℝ] E) × E) × (ℝ × ℝ) => (z.2.1 • z.1.1,z.2.2 • z.1.2)) ''
    (K ×ˢ (Icc a₀ a₁ ×ˢ Icc b₀ b₁))

/-- The genuine positive lift is compact. Article: s7:N. -/
theorem scaledReferenceCompact_isCompact (K : Set ((E →L[ℝ] E) × E))
    (hK : IsCompact K) (a₀ a₁ b₀ b₁ : ℝ) :
    IsCompact (scaledReferenceCompact K a₀ a₁ b₀ b₁) := by
  apply (hK.prod (isCompact_Icc.prod isCompact_Icc)).image
  exact (continuous_snd.fst.smul continuous_fst.fst).prodMk
    (continuous_snd.snd.smul continuous_fst.snd)

/-- Positive compact lifting preserves exactly the original full-CG
nondegeneracy, with true operators and true gradients. Article: s7:N. -/
theorem scaledReferenceCompact_nondegenerate (K : Set ((E →L[ℝ] E) × E))
    (N : ℕ) (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0)
    (a₀ a₁ b₀ b₁ : ℝ) (ha : 0<a₀) (hb : 0<b₀) :
    ∀ z∈scaledReferenceCompact K a₀ a₁ b₀ b₁, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<N, CG.gradient z.1 z.2 i≠0 := by
  rintro z ⟨⟨q,a,b⟩,⟨hq,ha',hb'⟩,rfl⟩
  have ha₁ : 0<a := ha.trans_le ha'.1
  have hb₁ : 0<b := hb.trans_le hb'.1
  have hs := (hquad q hq).1
  refine ⟨?_,?_,positive_scaled_reference_nondegenerate q.1 hs (hquad q hq).2.1
    q.2 a b ha₁ hb₁ N (hquad q hq).2.2⟩
  · intro x y
    change inner ℝ ((a • q.1) x) y=inner ℝ x ((a • q.1) y)
    simp only [_root_.smul_apply,real_inner_smul_left,real_inner_smul_right]
    exact congrArg (fun t : ℝ => a*t) (hs.apply_clm x y)
  · intro v hv
    simpa only [_root_.smul_apply,real_inner_smul_right] using
      mul_pos ha₁ ((hquad q hq).2.1 v hv)

/-- A true physical pair is covered by its normalized pair and its two
actual norm scales. No spectral coordinates are chosen. Article: s7:N. -/
theorem mem_scaledReferenceCompact (K : Set ((E →L[ℝ] E) × E))
    (A : E →L[ℝ] E) (g : E) (a₀ a₁ b₀ b₁ : ℝ)
    (hK : normalizedReference A g∈K) (ha : ‖A‖∈Icc a₀ a₁) (hb : ‖g‖∈Icc b₀ b₁) :
    (A,g)∈scaledReferenceCompact K a₀ a₁ b₀ b₁ := by
  refine ⟨(normalizedReference A g,‖A‖,‖g‖),⟨hK,ha,hb⟩,?_⟩
  simp only [normalizedReference,norm_smul_normalize]

end
end krylov.Functions
