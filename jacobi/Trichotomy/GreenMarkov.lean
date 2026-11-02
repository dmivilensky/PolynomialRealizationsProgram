import jacobi.Comparison.GreenLimit
import jacobi.Trichotomy.PhysicalProfile
import chebyshev2.Green.Markov

/-!
Article: jacobi, Proposition 2.2.
The original continuous target Green kernel inherits nonnegativity
and the exact one-dimensional Markov identity from the actual finite
Jacobi resolvents. The passage uses their already proved full entry limits.
Use: GreenPositivity and GreenExponential identify the complete original
kernel with its exponential-coordinate representation.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter Matrix jacobi.Reference jacobi.GelfandLevitan jacobi.Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The canonical target chain has a genuinely positive endpoint resolvent pencil.
Use: transfers the earlier article's exact finite inverse identities to the actual canonical chains.
Article: jacobi, Proposition 2.2.
Proof: the actual full fibre fixes its spectrum inside (-1,1), so the real spectral theorem makes the affine pencil positive definite. -/
theorem target_pencil_posDef (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    (1-(targetChain a b ha hb n).matrix).PosDef := by
  have h := (targetChain a b ha hb n).affine_posDef 1 (-1) (fun x hx => by
    rw [(jacobi.Jacobi.nodes a b ha hb (n+1)).spectrum_eq (targetChain_inFiber a b ha hb n)] at hx
    obtain ⟨i,rfl⟩ := hx
    linarith [((jacobi.Jacobi.nodes a b ha hb (n+1)).interval i).2])
  simpa [Matrix.scalar,sub_eq_add_neg] using h

/-- Every actual full target Green entry is nonnegative in the physical interior.
Use: GreenPositivity strengthens this to strict positivity using the positive original diagonal and the exact Markov identity.
Article: jacobi, Proposition 2.2.
Proof: every genuine finite inverse entry is strictly positive. Its proved full normalized entry limit is twice the actual target Green kernel, so that limit is nonnegative. -/
theorem targetGreen_nonneg (a:ℝ) (ha:-1<a) (t s:ℝ)
    (ht:t∈Ioo (0:ℝ) 1) (hs:s∈Ioo (0:ℝ) 1) :
    0≤targetGreenKernel a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩ ⟨s,⟨hs.1.le,hs.2.le⟩⟩ := by
  -- Pass the actual finite nonnegative Green entries to the genuine continuum kernel limit.
  have hb : (-1:ℝ)<0 := by norm_num
  have hl := scaledTargetGreen_floor_limit ha hb t s ht hs
  have hn : ∀ n:ℕ,0≤scaledTargetGreen a 0 ha hb n
      (jacobi.Analysis.floorMatrixIndex n t ht) (jacobi.Analysis.floorMatrixIndex n s hs) := by
    intro n
    exact div_nonneg ((targetChain a 0 ha hb n).green_entry_pos
      (target_pencil_posDef a 0 ha hb n) (targetChain_inFiber a 0 ha hb n).1 _ _).le (by positivity)
  have he := ge_of_tendsto hl (Eventually.of_forall hn)
  linarith

/-- The actual continuous full Green kernel satisfies its exact ordered multiplicative identity.
Use: the positive kernel is factored and identified with the intrinsic exponential coordinate in Proposition 2.2.
Article: jacobi, Proposition 2.2.
Proof: the original finite tridiagonal inverse has precisely this cofactor identity. Positive dimension normalization preserves it. Pass to the four genuine full matrix-entry limits at the physical floor rows. -/
theorem targetGreen_markov (a:ℝ) (ha:-1<a) (t s u:ℝ)
    (ht:t∈Ioo (0:ℝ) 1) (hs:s∈Ioo (0:ℝ) 1) (hu:u∈Ioo (0:ℝ) 1)
    (hts:t≤s) (hsu:s≤u) :
    targetGreenKernel a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩ ⟨u,⟨hu.1.le,hu.2.le⟩⟩*
      targetGreenKernel a ha ⟨s,⟨hs.1.le,hs.2.le⟩⟩ ⟨s,⟨hs.1.le,hs.2.le⟩⟩=
    targetGreenKernel a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩ ⟨s,⟨hs.1.le,hs.2.le⟩⟩*
      targetGreenKernel a ha ⟨s,⟨hs.1.le,hs.2.le⟩⟩ ⟨u,⟨hu.1.le,hu.2.le⟩⟩ := by
  -- Use the finite cofactor identity at the three ordered mesh points, then pass its products to the limit.
  -- All four factors are entries of the same genuine original inverse before the common limit is taken.
  have hb : (-1:ℝ)<0 := by norm_num
  let R := fun n (x:ℝ) (hx:x∈Ioo (0:ℝ) 1) (y:ℝ) (hy:y∈Ioo (0:ℝ) 1) =>
    scaledTargetGreen a 0 ha hb n (jacobi.Analysis.floorMatrixIndex n x hx) (jacobi.Analysis.floorMatrixIndex n y hy)
  have he (n:ℕ) : R n t ht u hu*R n s hs s hs=R n t ht s hs*R n s hs u hu := by
    have h := (targetChain a 0 ha hb n).green_markov (target_pencil_posDef a 0 ha hb n)
      (jacobi.Analysis.floorMatrixIndex n t ht) (jacobi.Analysis.floorMatrixIndex n s hs)
      (jacobi.Analysis.floorMatrixIndex n u hu)
      (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hts (by positivity)))
      (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hsu (by positivity)))
    dsimp [R,scaledTargetGreen]
    rw [div_mul_div_comm,div_mul_div_comm,h]
  have hL := (scaledTargetGreen_floor_limit ha hb t u ht hu).mul
    (scaledTargetGreen_floor_limit ha hb s s hs hs)
  have hR := (scaledTargetGreen_floor_limit ha hb t s ht hs).mul
    (scaledTargetGreen_floor_limit ha hb s u hs hu)
  have hh := tendsto_nhds_unique ((tendsto_congr (fun n => he n)).mp hL) hR
  nlinarith [hh]

end
end jacobi.Trichotomy
