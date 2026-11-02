import krylov.LinearAlgebra.PlanarWitness
import krylov.LinearAlgebra.FrobeniusAggregation

/-!
Article: Lemma B.2 [lem:aggregate] of krylov.tex.
Use: verify the actual common-plane perturbation outputs for arbitrary old
subspaces containing the same direction, rather than postulating sharpness data.
Source: the printed planar constructions, proved through actual matrix actions.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Finset chebyshev1
open scoped Matrix BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} {n : ℕ}

/-- A common old-subspace direction is orthogonal to the hidden unit direction whenever an old flag exists.
Use: the article's stated common-direction hypothesis supplies the orthogonality used in both witnesses.
Article: main_krylov, lem:aggregate, simultaneous-sharpness hypothesis.
Proof: test membership of h in one actual old subspace's orthogonal complement on e. -/
theorem common_old_directions_orthogonal (I : Finset ι) (hI : I.Nonempty)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (e h : EuclideanSpace ℝ (Fin n))
    (heK : ∀ i ∈ I, e ∈ K i) (hhK : ∀ i ∈ I, h ∈ (K i)ᗮ) : inner ℝ e h = 0 := by
  obtain ⟨i, hi⟩ := hI
  exact ((K i).mem_orthogonal h).mp (hhK i hi) e (heK i hi)

/-- An empty old-flag family has an actual admissible zero witness and all three aggregate outputs vanish.
Use: the degenerate sharpness case requires no second orthogonal physical direction.
Article: main_krylov, lem:aggregate, empty-index and zero-sum boundary.
Proof: choose the actual zero matrix family and evaluate the empty finite sums. -/
theorem empty_aggregate_attainment
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (h : EuclideanSpace ℝ (Fin n)) (ω : ι → ℝ) :
    ∃ E : ι → Matrix (Fin n) (Fin n) ℝ,
      (∀ i ∈ (∅ : Finset ι), (E i).IsSymm ∧ opNorm (E i) ≤ ω i ∧ hsNorm (E i) ≤ ω i) ∧
      let T := fun i => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E i)
      let X := ∑ i ∈ (∅ : Finset ι), (K i).starProjection (T i h)
      X = 0 ∧ (∑ i ∈ (∅ : Finset ι), (K i).starProjection (T i ((K i).starProjection X))) = 0 ∧
        (∑ i ∈ (∅ : Finset ι), inner ℝ h (T i h)) = 0 := by
  exact ⟨0, by simp, by simp⟩

/-- Scaling all three actual planar block coefficients scales its physical matrix.
Use: each attaining increment carries exactly its assigned scalar budget.
Article: main_krylov, lem:aggregate, E_l=ω_lE.
Proof: distribute the real scalar through the three actual outer terms. -/
theorem planarMatrix_scale (e h : EuclideanSpace ℝ (Fin n)) (ω a b c : ℝ) :
    planarMatrix e h (ω*a) (ω*b) (ω*c) = ω • planarMatrix e h a b c := by
  simp only [planarMatrix, smul_add, smul_smul]

/-- Actual planar increments have the stated cross, old-subspace and hidden diagonal actions.
Use: one common direction in every old subspace gives the printed simultaneous witnesses.
Article: main_krylov, lem:aggregate, planar attaining blocks.
Proof: evaluate the two actual matrix actions, then use Pe=e and Ph=0. -/
theorem projected_planar_actions (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [K.HasOrthogonalProjection] (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖ = 1) (hh : ‖h‖ = 1) (heh : inner ℝ e h = 0) (heK : e ∈ K) (hhK : h ∈ Kᗮ)
    (a b c α : ℝ) :
    let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (planarMatrix e h a b c)
    K.starProjection (T h) = b • e ∧
      K.starProjection (T (K.starProjection (α • e))) = (α*a) • e ∧ inner ℝ h (T h) = c := by
  dsimp only
  have hhe : inner ℝ h e = 0 := by rw [real_inner_comm]; exact heh
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hhh : inner ℝ h h = 1 := by rw [real_inner_self_eq_norm_sq, hh, one_pow]
  have hPe : K.starProjection e = e := K.starProjection_eq_self_iff.mpr heK
  have hPh : K.starProjection h = 0 := K.starProjection_apply_eq_zero_iff.mpr hhK
  -- Every old projector agrees on the two actual witness directions.
  simp only [map_smul, map_add, planarMatrix_action, hee, hhh, heh, hhe, hPe, hPh,
    mul_zero, mul_one, zero_add, add_zero, smul_zero, smul_smul, inner_add_right,
    real_inner_smul_right, true_and]

/-- The actual budget-scaled planar family has its three exact aggregate outputs.
Use: certify simultaneous sharpness using the actual sum X, compressed action YX and hidden γ.
Article: main_krylov, lem:aggregate, both printed attaining families.
Proof: apply each genuine projected planar action and sum its physical coefficients. -/
theorem planar_aggregate_values (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) (hh : ‖h‖ = 1) (heh : inner ℝ e h = 0)
    (heK : ∀ i ∈ I, e ∈ K i) (hhK : ∀ i ∈ I, h ∈ (K i)ᗮ)
    (ω : ι → ℝ) (a b c : ℝ) :
    let T := fun i => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (planarMatrix e h (ω i*a) (ω i*b) (ω i*c))
    let X := ∑ i ∈ I, (K i).starProjection (T i h)
    let W := ∑ i ∈ I, ω i
    X = (W*b) • e ∧
      (∑ i ∈ I, (K i).starProjection (T i ((K i).starProjection X))) = (W^2*a*b) • e ∧
      (∑ i ∈ I, inner ℝ h (T i h)) = W*c := by
  dsimp only
  let T := fun i => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (planarMatrix e h (ω i*a) (ω i*b) (ω i*c))
  let W := ∑ i ∈ I, ω i
  have hx : (∑ i ∈ I, (K i).starProjection (T i h)) = (W*b) • e := by
    calc
      _ = ∑ i ∈ I, (ω i*b) • e := sum_congr rfl fun i hi =>
        (projected_planar_actions (K i) e h he hh heh (heK i hi) (hhK i hi) _ _ _ 0).1
      _ = _ := by rw [← sum_smul, ← sum_mul]
  refine ⟨hx, ?_, ?_⟩
  · rw [hx]
    -- All old compressions act on the same actual aggregate cross direction.
    calc
      _ = ∑ i ∈ I, ((W*b)*(ω i*a)) • e := sum_congr rfl fun i hi =>
        (projected_planar_actions (K i) e h he hh heh (heK i hi) (hhK i hi) _ _ _ (W*b)).2.1
      _ = ((W*b*a)*W) • e := by
        change _ = ((W*b*a)*(∑ i ∈ I, ω i)) • e
        rw [mul_sum, sum_smul]
        apply sum_congr rfl
        intro i _
        congr 1
        ring
      _ = _ := by congr 1; ring
  · calc
      _ = ∑ i ∈ I, ω i*c := sum_congr rfl fun i hi =>
        (projected_planar_actions (K i) e h he hh heh (heK i hi) (hhK i hi) _ _ _ 0).2.2
      _ = _ := (sum_mul _ _ _).symm

/-- The actual scaled unit-circle parameters give the exact sharp square root.
Use: identify the printed aggregate radius from the actual constructed witness outputs.
Article: main_krylov, lem:aggregate, simultaneous sharpness.
Proof: the radicand is exactly the square of the nonnegative scaled complementary parameter. -/
theorem scaled_circle_sqrt (W s t : ℝ) (hW : 0 ≤ W) (hs : 0 ≤ s) (hst : s^2+t^2=1) :
    Real.sqrt (W^2-(W*t)^2) = W*s := by
  have hr : W^2-(W*t)^2 = (W*s)^2 := by
    calc
      _ = W^2*(1-t^2) := by ring
      _ = W^2*s^2 := by rw [show 1-t^2=s^2 by linarith]
      _ = _ := by ring
  rw [hr, Real.sqrt_sq (mul_nonneg hW hs)]

/-- The actual spectral planar family simultaneously attains both sharp tradeoff bounds,
and realizes every cross norm Wt on the nonnegative unit circle.
Use: the sharpness assertion holds for arbitrary old subspaces sharing e, not just coordinate examples.
Article: main_krylov, lem:aggregate, spectral simultaneous sharpness.
Proof: verify every actual symmetric norm budget, use the proved physical planar
aggregate identities, and identify the complementary radius by the unit-circle equation. -/
theorem spectral_aggregate_sharpness (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) (hh : ‖h‖ = 1) (heh : inner ℝ e h = 0)
    (heK : ∀ i ∈ I, e ∈ K i) (hhK : ∀ i ∈ I, h ∈ (K i)ᗮ)
    (ω : ι → ℝ) (hω : ∀ i ∈ I, 0 ≤ ω i) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s^2+t^2=1) :
    ∃ E : ι → Matrix (Fin n) (Fin n) ℝ,
      (∀ i ∈ I, (E i).IsSymm ∧ opNorm (E i) ≤ ω i) ∧
      let T := fun i => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E i)
      let X := ∑ i ∈ I, (K i).starProjection (T i h)
      let W := ∑ i ∈ I, ω i
      ‖X‖ = W*t ∧
        ‖∑ i ∈ I, (K i).starProjection (T i ((K i).starProjection X))‖ =
          ‖X‖*Real.sqrt (W^2-‖X‖^2) ∧
        |∑ i ∈ I, inner ℝ h (T i h)| = Real.sqrt (W^2-‖X‖^2) := by
  let E := fun i => planarMatrix e h (ω i*(-s)) (ω i*t) (ω i*s)
  have hW : 0 ≤ ∑ i ∈ I, ω i := sum_nonneg hω
  have hv := planar_aggregate_values I K e h he hh heh heK hhK ω (-s) t s
  refine ⟨E, ?_, ?_⟩
  · intro i hi
    refine ⟨planarMatrix_isSymm _ _ _ _ _, ?_⟩
    change opNorm (planarMatrix e h (ω i*(-s)) (ω i*t) (ω i*s)) ≤ ω i
    rw [planarMatrix_scale, opNorm_smul, abs_of_nonneg (hω i hi)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (planar_spectral_norm_le e h he hh heh s t hst) (hω i hi)
  · dsimp only [E]
    dsimp only at hv
    -- All three outputs come from the same actual physical matrix family.
    rw [hv.2.1, hv.1, hv.2.2]
    simp only [norm_smul, Real.norm_eq_abs, he, mul_one]
    rw [abs_of_nonneg (mul_nonneg hW ht), scaled_circle_sqrt _ _ _ hW hs hst,
      abs_of_nonneg (mul_nonneg hW hs)]
    have hy : (∑ i ∈ I, ω i)^2*(-s)*t = -((∑ i ∈ I, ω i)^2*s*t) := by ring
    rw [hy, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hs) ht)]
    exact ⟨rfl, by ring, rfl⟩

/-- The actual Frobenius planar family attains the improved aggregate action bound
and realizes every cross norm Wt/√2 on the nonnegative unit circle.
Use: construct the source's simultaneous Frobenius sharpness instances in arbitrary old subspaces.
Article: main_krylov, lem:aggregate, Frobenius simultaneous sharpness.
Proof: the actual three-coefficient Frobenius energy verifies every budget;
the same physical planar aggregate identities give the exact improved radius. -/
theorem frobenius_aggregate_sharpness (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) (hh : ‖h‖ = 1) (heh : inner ℝ e h = 0)
    (heK : ∀ i ∈ I, e ∈ K i) (hhK : ∀ i ∈ I, h ∈ (K i)ᗮ)
    (ω : ι → ℝ) (hω : ∀ i ∈ I, 0 ≤ ω i) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s^2+t^2=1) :
    ∃ E : ι → Matrix (Fin n) (Fin n) ℝ,
      (∀ i ∈ I, (E i).IsSymm ∧ hsNorm (E i) ≤ ω i) ∧
      let T := fun i => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E i)
      let X := ∑ i ∈ I, (K i).starProjection (T i h)
      let W := ∑ i ∈ I, ω i
      Real.sqrt 2 * ‖X‖ = W*t ∧
        ‖∑ i ∈ I, (K i).starProjection (T i ((K i).starProjection X))‖ =
          ‖X‖*Real.sqrt (W^2-2*‖X‖^2) := by
  let b := t / Real.sqrt 2
  let E := fun i => planarMatrix e h (ω i*s) (ω i*b) (ω i*0)
  have hW : 0 ≤ ∑ i ∈ I, ω i := sum_nonneg hω
  have hsq : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hb : 0 ≤ b := div_nonneg ht hr.le
  have hb2 : 2*b^2 = t^2 := by dsimp only [b]; rw [div_pow, hsq]; ring
  have hnorm : hsNorm (planarMatrix e h s b 0) = 1 := by
    have hn := hsNorm_sq (planarMatrix e h s b 0)
    rw [planar_hsSq e h he hh heh, hb2] at hn
    nlinarith [hsNorm_nonneg (planarMatrix e h s b 0)]
  have hv := planar_aggregate_values I K e h he hh heh heK hhK ω s b 0
  refine ⟨E, ?_, ?_⟩
  · intro i hi
    refine ⟨planarMatrix_isSymm _ _ _ _ _, ?_⟩
    change hsNorm (planarMatrix e h (ω i*s) (ω i*b) (ω i*0)) ≤ ω i
    rw [planarMatrix_scale, hsNorm_smul, abs_of_nonneg (hω i hi), hnorm, mul_one]
  · dsimp only [E]
    dsimp only at hv
    -- The genuine Frobenius-budget matrices have the exact same common-plane aggregate actions.
    rw [hv.2.1, hv.1]
    simp only [norm_smul, Real.norm_eq_abs, he, mul_one,
      abs_of_nonneg (mul_nonneg hW hb), abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hs) hb)]
    have hrad : 2*((∑ i ∈ I, ω i)*b)^2 = ((∑ i ∈ I, ω i)*t)^2 := by
      calc
        _ = (∑ i ∈ I, ω i)^2*(2*b^2) := by ring
        _ = _ := by rw [hb2]; ring
    rw [hrad, scaled_circle_sqrt _ _ _ hW hs hst]
    constructor
    · dsimp only [b]
      field_simp
    · ring

end
end krylov.LinearAlgebra
