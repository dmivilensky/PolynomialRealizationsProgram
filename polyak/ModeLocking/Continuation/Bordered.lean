import polyak.ModeLocking.Continuation.ClassSums

/-! The bordered primal system has an invertible derivative. This is the
linear algebra behind continuing the shift and normalized right kernel together. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def borderedMap (b : Fin D.d → ℝ) :
    (ℝ × (Fin D.d → ℝ)) →ₗ[ℝ] ((Fin D.d → ℝ) × ℝ) where
  toFun p := (D.matrix.mulVec p.2 + p.1 • b, ∑ i, p.2 i)
  map_add' p v := by
    ext i
    · simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, add_smul, Prod.fst_add]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c p := by
    ext i
    · change (D.matrix.mulVec (c • p.2) + (c * p.1) • b) i = c * (D.matrix.mulVec p.2 + p.1 • b) i
      rw [Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · change (∑ i, c * p.2 i) = c * ∑ i, p.2 i
      exact (Finset.mul_sum _ _ _).symm

theorem left_kernel_annihilates (v : Fin D.d → ℝ) :
    (∑ r, D.classWeight r * D.matrix.mulVec v r) = 0 := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have hcol := congrFun D.matrix_transpose_mul_classWeight i
  change (∑ r, D.matrix r i * D.classWeight r) = 0 at hcol
  calc
    ∑ r, D.classWeight r * (D.matrix r i * v i) =
      (∑ r, D.matrix r i * D.classWeight r) * v i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        ring
    _ = 0 := by rw [hcol, zero_mul]

theorem bordered_injective (b : Fin D.d → ℝ)
    (hb : (∑ r, D.classWeight r * b r) ≠ 0) : Function.Injective (D.borderedMap b) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨t, v⟩ he
  have hm := congrArg Prod.fst he
  have hn := congrArg Prod.snd he
  change D.matrix.mulVec v + t • b = 0 at hm
  change ∑ i, v i = 0 at hn
  have hsum := congrArg (fun z : Fin D.d → ℝ => ∑ r, D.classWeight r * z r) hm
  have hsum' : (∑ r, D.classWeight r * D.matrix.mulVec v r) +
      t * ∑ r, D.classWeight r * b r = 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
      using hsum
  rw [D.left_kernel_annihilates, zero_add] at hsum'
  have ht : t = 0 := (mul_eq_zero.mp hsum').resolve_right hb
  rw [ht, zero_smul, add_zero] at hm
  obtain ⟨c, hc⟩ := D.kernel_unique hm
  have hnorm : ∑ i, (D.primal i : ℝ) = 1 := by exact_mod_cast D.primal_sum
  have hvc : (∑ i, v i) = c := by
    simp only [hc, ← Finset.mul_sum, hnorm, mul_one]
  have hcz : c = 0 := hvc.symm.trans hn
  apply Prod.ext ht
  funext i
  change v i = 0
  rw [hc, hcz, zero_mul]

def borderedEquiv (b : Fin D.d → ℝ) (hb : (∑ r, D.classWeight r * b r) ≠ 0) :
    (ℝ × (Fin D.d → ℝ)) ≃L[ℝ] ((Fin D.d → ℝ) × ℝ) :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective (D.borderedMap b)
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_prod, add_comm])).mp (D.bordered_injective b hb) |>
      fun hs => ⟨D.bordered_injective b hb, hs⟩))

end polyak.ModeLocking.RegularData
