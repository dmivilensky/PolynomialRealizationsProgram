import krylov.Methods.VirtualSolve
import krylov.Reference.PolynomialAction

/-!
Article: main_krylov, lem:consistent(b), computed CG flag geometry.
Use: transport actual virtual-launch step bases to the already proved true
Krylov flags, without presupposing that virtual outputs follow CG.
Source: the actual CG invariants and elementary span extension by a nonzero trial.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual span of the true first k computed reference CG directions.
Use: the actual XRFC stored step basis is proved to generate this flag.
Article: main_krylov, lem:consistent(b), K_k. -/
def directionFlag (Q : E →L[ℝ] E) (g : E) (k : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (CG.direction Q g '' Set.Iio k)

/-- The empty actual reference direction flag is zero.
Use: initialize the actual virtual-launch basis induction.
Article: main_krylov, lem:consistent(b).
Proof: there are no direction indices before zero. -/
theorem directionFlag_zero (Q : E →L[ℝ] E) (g : E) : directionFlag Q g 0=⊥ := by
  have hz : Set.Iio (0 : ℕ)=∅ := by ext i; simp
  rw [directionFlag, hz, Set.image_empty, Submodule.span_empty]

/-- The genuine next CG flag adds exactly its actual current reference direction.
Use: any nonzero actual XRFC trial must add precisely this next direction.
Article: main_krylov, lem:consistent(b), Krylov flag growth.
Proof: an index before k+1 is either k or an earlier index. -/
theorem directionFlag_succ (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    directionFlag Q g (k+1)=(ℝ ∙ CG.direction Q g k)⊔directionFlag Q g k := by
  -- Split the actual generating image at its newest chronological direction.
  have he : CG.direction Q g '' Set.Iio (k+1)=insert (CG.direction Q g k) (CG.direction Q g '' Set.Iio k) := by
    ext v
    constructor
    · rintro ⟨i,hi,rfl⟩
      by_cases h : i=k
      · exact Or.inl (congrArg _ h)
      · exact Or.inr ⟨i,by change i<k+1 at hi; change i<k; omega,rfl⟩
    · rintro (rfl | ⟨i,hi,rfl⟩)
      · exact ⟨k,Nat.lt_succ_self k,rfl⟩
      · exact ⟨i,by change i<k at hi; change i<k+1; omega,rfl⟩
  rw [directionFlag, he, Submodule.span_insert]
  rfl

/-- True current CG residuals annihilate the full actual old direction flag.
Use: the actual virtual model solve is characterized by the true Galerkin residual.
Article: main_krylov, lem:consistent(b), g_k⁰ orthogonal to K_k.
Proof: the computed CG invariant annihilates every old generator and hence their entire actual span. -/
theorem directionFlag_gradient_orthogonal (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) {v : E} (hv : v∈directionFlag Q g k) :
    inner ℝ v (CG.gradient Q g k)=0 := by
  -- Orthogonality on actual generators extends by the kernel submodule property.
  have hle : directionFlag Q g k≤(innerSL ℝ (CG.gradient Q g k)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change inner ℝ (CG.gradient Q g k) (CG.direction Q g i)=0
    rw [real_inner_comm]
    exact (CG.invariant Q hQ hpos g k hg).old_direction i hi
  have he := hle hv
  change inner ℝ (CG.gradient Q g k) v=0 at he
  rwa [real_inner_comm] at he

/-- True current CG directions are conjugate to their complete actual old direction flag.
Use: identify a computed block conjugacy solve on any independent basis of the actual flag.
Article: main_krylov, lem:consistent(b), current conjugacy.
Proof: true pairwise conjugacy annihilates every generator of the full old flag. -/
theorem directionFlag_conjugate (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) {v : E} (hv : v∈directionFlag Q g k) :
    inner ℝ v (Q (CG.direction Q g k))=0 := by
  -- True pairwise conjugacy annihilates the span of all earlier actual directions.
  have hle : directionFlag Q g k≤(innerSL ℝ (Q (CG.direction Q g k))).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change inner ℝ (Q (CG.direction Q g k)) (CG.direction Q g i)=0
    rw [real_inner_comm]
    exact (CG.invariant Q hQ hpos g k hg).conjugate i k hi le_rfl
  have he := hle hv
  change inner ℝ (Q (CG.direction Q g k)) v=0 at he
  rwa [real_inner_comm] at he

/-- The true reference displacement belongs to its actual old direction flag.
Use: its difference from any actual stored-span evaluated point is an admissible virtual correction.
Article: main_krylov, lem:consistent(b), x_k⁰∈x₀+K_k.
Proof: every actual reference step is a scalar multiple of one old flag generator. -/
theorem displacement_mem_directionFlag (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    CG.displacement Q g k∈directionFlag Q g k := by
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,Finset.mem_range.mp hi,rfl⟩)

/-- The actual reference direction differs from the negative residual only within its actual old flag.
Use: computed conjugacy uniqueness identifies the true direction on arbitrary independent XRFC step bases.
Article: main_krylov, lem:consistent(b), d_k⁰+g_k⁰∈K_k.
Proof: the actual Fletcher--Reeves recurrence adds a scalar multiple of the previous actual direction. -/
theorem direction_add_gradient_mem_flag (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    CG.direction Q g k+CG.gradient Q g k∈directionFlag Q g k := by
  cases k with
  | zero => change -g+g∈_; rw [neg_add_cancel]; exact Submodule.zero_mem _
  | succ k =>
    have he : CG.direction Q g (k+1)+CG.gradient Q g (k+1)=CG.beta Q g k • CG.direction Q g k := by
      rw [CG.direction_succ]
      abel
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,Nat.lt_succ_self k,rfl⟩)

/-- Adding a nonzero trial in a new direction extends the same actual span as adding that direction itself.
Use: the actual recorded step may include any old-span virtual correction.
Article: main_krylov, lem:consistent(b), nonzero trial flag extension.
Proof: the new step is old correction plus the nonzero scaled new direction;
subtract the old correction and divide by the actual nonzero trial for the reverse inclusion. -/
theorem trial_span_extension (K : Submodule ℝ E) (u d : E) (hu : u∈K) (t : ℝ) (ht : t≠0) :
    (ℝ ∙ (u+t • d))⊔K=(ℝ ∙ d)⊔K := by
  -- The extension is independent of the actual trial magnitude, provided it is nonzero.
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply Submodule.span_le.mpr
    intro v hv
    have hv' : v=u+t • d := hv
    rw [hv']
    exact Submodule.add_mem _ ((show K≤(ℝ ∙ d)⊔K from le_sup_right) hu)
      (Submodule.smul_mem _ _ ((show (ℝ ∙ d)≤(ℝ ∙ d)⊔K from le_sup_left) (Submodule.mem_span_singleton_self d)))
  · apply sup_le _ le_sup_right
    apply Submodule.span_le.mpr
    intro v hv
    have hv' : v=d := hv
    rw [hv']
    have hs : u+t • d∈(ℝ ∙ (u+t • d))⊔K :=
      (show (ℝ ∙ (u+t • d))≤(ℝ ∙ (u+t • d))⊔K from le_sup_left) (Submodule.mem_span_singleton_self _)
    have hu' : u∈(ℝ ∙ (u+t • d))⊔K := (show K≤(ℝ ∙ (u+t • d))⊔K from le_sup_right) hu
    have hd := Submodule.smul_mem ((ℝ ∙ (u+t • d))⊔K) t⁻¹ (Submodule.sub_mem _ hs hu')
    have he : t⁻¹ • ((u+t • d)-u)=d := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [he] at hd
    exact hd

end
end krylov.Methods
