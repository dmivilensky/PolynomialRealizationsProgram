import krylov.LinearAlgebra.SymmetricBall
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.MeanInequalities

/-!
Article: main_krylov, apA:galerkin(e), symmetric uncertainty support and budget allocation.
Use: separate the actual symmetric-operator support problem from its finite Hölder
allocation, with attaining operators rather than a norm bound alone.
Source: Rump03 for the symmetric ball; mathlib NNReal.isGreatest_Lp for sharp finite Hölder duality.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Finset
open scoped InnerProductSpace BigOperators NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A real vector pairs with its actual normalized direction to give its norm, also at zero.
Use: choose the attaining direction for a symmetric uncertainty support functional.
Article: main_krylov, apA:galerkin(e), single-budget support.
Proof: in the nonzero case cancel its positive norm in the squared self-pairing. -/
theorem inner_normalize (u : E) : inner ℝ u (NormedSpace.normalize u) = ‖u‖ := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_sq,
      pow_two, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu), one_mul]

/-- The support of the actual selfadjoint operator ball is the product of the two vector norms.
Use: the exact spectral-budget support, with an admissible attaining symmetric operator.
Article: main_krylov, apA:galerkin(e), max_E ⟨u,Ev⟩=Ω‖u‖‖v‖.
Proof: Cauchy--Schwarz and the true operator norm give the upper bound; the
proved symmetric-ball construction maps v to Ω‖v‖ times the normalized u. -/
theorem symmetric_ball_support (u v : E) {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    IsGreatest {z : ℝ | ∃ T : E →L[ℝ] E, IsSelfAdjoint T ∧ ‖T‖ ≤ Ω ∧
      z = inner ℝ u (T v)} (Ω * ‖u‖ * ‖v‖) := by
  let w := (Ω * ‖v‖) • NormedSpace.normalize u
  have hn : ‖NormedSpace.normalize u‖ ≤ 1 := by
    by_cases hu : u = 0
    · simp [hu]
    · exact (NormedSpace.norm_normalize hu).le
  have hw : ‖w‖ ≤ Ω * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hΩ (norm_nonneg _))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (mul_nonneg hΩ (norm_nonneg _))
  obtain ⟨T, hT, hbound, hmap⟩ := exists_selfAdjoint_image v w hΩ hw
  constructor
  · refine ⟨T, hT, hbound, ?_⟩
    rw [hmap, real_inner_smul_right, inner_normalize]
    ring
  · rintro z ⟨S, _, hS, rfl⟩
    -- The upper bound uses the actual queried action, without choosing its sign in advance.
    have hs := ((S.le_opNorm v).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg v)))
    have hi := (real_inner_le_norm u (S v)).trans
      (mul_le_mul_of_nonneg_left hs (norm_nonneg u))
    nlinarith

variable {ι : Type*}

/-- Genuine symmetric perturbations admitting a nonnegative scalar budget allocation.
Use: one definition treats finite ℓ_p budgets, box budgets and simplex budgets,
and forces every zero-budget operator to vanish through its actual norm bound.
Article: main_krylov, apA:galerkin(e), admissible symmetric increments. -/
def symmetricBudgetFamily (I : Finset ι) (ω : ι → ℝ≥0) (B : Set (ι → ℝ≥0)) :
    Set (ι → E →L[ℝ] E) :=
  {T | ∃ a ∈ B, ∀ i ∈ I, IsSelfAdjoint (T i) ∧ ‖T i‖ ≤ (ω i * a i : ℝ≥0)}

/-- Any attained scalar allocation support lifts to the exact attained support of actual
symmetric operator budgets.
Use: reduce spectral budget duality to the existing sharp finite Hölder theorem.
Article: main_krylov, apA:galerkin(e), budget support at a fixed output direction.
Proof: for the maximizing allocation construct one actual symmetric-ball maximizer
per increment; every admissible family has some allocation and obeys the same scalar bound. -/
theorem symmetric_budget_support (I : Finset ι) (ω : ι → ℝ≥0) (B : Set (ι → ℝ≥0))
    (u v : ι → E) (C : ℝ≥0)
    (hC : IsGreatest ((fun a : ι → ℝ≥0 => ∑ i ∈ I, (ω i * ‖u i‖₊ * ‖v i‖₊) * a i) '' B) C) :
    IsGreatest {z : ℝ | ∃ T ∈ symmetricBudgetFamily I ω B,
      z = ∑ i ∈ I, inner ℝ (u i) (T i (v i))} (C : ℝ) := by
  obtain ⟨a, ha, hmax⟩ := hC.1
  have hlocal : ∀ i, ∃ T : E →L[ℝ] E, IsSelfAdjoint T ∧ ‖T‖ ≤ (ω i * a i : ℝ≥0) ∧
      inner ℝ (u i) (T (v i)) = (ω i * a i : ℝ≥0) * ‖u i‖ * ‖v i‖ := by
    intro i
    obtain ⟨T, hT, hb, he⟩ := (symmetric_ball_support (u i) (v i) (Ω := (ω i * a i : ℝ≥0))
      (NNReal.coe_nonneg _)).1
    exact ⟨T, hT, hb, he.symm⟩
  choose T hsym hnorm hvalue using hlocal
  have hsum : ∑ i ∈ I, (ω i * a i : ℝ≥0) * ‖u i‖ * ‖v i‖ =
      ((∑ i ∈ I, (ω i * ‖u i‖₊ * ‖v i‖₊) * a i : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm]
    apply sum_congr rfl
    intro i _
    ring
  constructor
  · refine ⟨T, ⟨a, ha, fun i _ => ⟨hsym i, hnorm i⟩⟩, ?_⟩
    rw [← hmax, ← hsum]
    exact (sum_congr rfl fun i _ => hvalue i).symm
  · rintro z ⟨S, ⟨b, hb, hS⟩, rfl⟩
    -- Every actual operator family is controlled by its genuine allocating vector b.
    have hi : ∀ i ∈ I, inner ℝ (u i) (S i (v i)) ≤
        (ω i * b i : ℝ≥0) * ‖u i‖ * ‖v i‖ := by
      intro i hi
      exact (symmetric_ball_support (u i) (v i) (Ω := (ω i * b i : ℝ≥0))
        (NNReal.coe_nonneg _)).2 ⟨S i, (hS i hi).1, (hS i hi).2, rfl⟩
    have hbmax : (∑ i ∈ I, (ω i * ‖u i‖₊ * ‖v i‖₊) * b i : ℝ≥0) ≤ C :=
      hC.2 ⟨b, hb, rfl⟩
    apply (sum_le_sum hi).trans
    have he : ∑ i ∈ I, (ω i * b i : ℝ≥0) * ‖u i‖ * ‖v i‖ =
        ((∑ i ∈ I, (ω i * ‖u i‖₊ * ‖v i‖₊) * b i : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm]
      apply sum_congr rfl
      intro i _
      ring
    rw [he]
    exact_mod_cast hbmax

/-- Finite conjugate ℓ_p budgets have the sharp attained ℓ_q support in every fixed direction.
Use: the operator part of full spectral budget duality, including zero budgets.
Article: main_krylov, apA:galerkin(e), finite 1<p<∞ budget allocation.
Source: mathlib NNReal.isGreatest_Lp supplies the actual Hölder maximizing allocation.
Proof: instantiate the proved operator-support lifting with the existing sharp scalar duality. -/
theorem symmetric_lp_support (I : Finset ι) (ω : ι → ℝ≥0) (u v : ι → E)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    IsGreatest {z : ℝ | ∃ T ∈ symmetricBudgetFamily I ω {a | ∑ i ∈ I, (a i)^p ≤ 1},
      z = ∑ i ∈ I, inner ℝ (u i) (T i (v i))}
      (((∑ i ∈ I, (ω i * ‖u i‖₊ * ‖v i‖₊)^q : ℝ≥0) ^ (1 / q) : ℝ≥0) : ℝ) :=
  symmetric_budget_support I ω _ u v _
    (NNReal.isGreatest_Lp I (fun i => ω i * ‖u i‖₊ * ‖v i‖₊) hpq.symm)

/-- Allocation certificates are exactly the original normalized operator-norm budget,
with the article's required zero-budget convention.
Use: the support theorem above applies to actual perturbation norm constraints,
not a different or weaker uncertainty family.
Article: main_krylov, apA:galerkin(e), ‖(‖E_l‖/ω_l)_l‖_p≤1.
Proof: divide any actual allocated norm bound at nonzero budgets; conversely
allocate its actual normalized norm, forcing zero-budget operators to zero. -/
theorem symmetric_lp_family_iff (I : Finset ι) (ω : ι → ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (T : ι → E →L[ℝ] E) :
    T ∈ symmetricBudgetFamily I ω {a | ∑ i ∈ I, (a i)^p ≤ 1} ↔
      (∀ i ∈ I, IsSelfAdjoint (T i) ∧ (ω i = 0 → T i = 0)) ∧
      ∑ i ∈ I, (‖T i‖₊ / ω i)^p ≤ 1 := by
  constructor
  · rintro ⟨a, ha, hT⟩
    have hb : ∀ i ∈ I, ‖T i‖₊ ≤ ω i * a i := by
      intro i hi
      exact_mod_cast (hT i hi).2
    refine ⟨?_, (sum_le_sum (fun i hi => NNReal.rpow_le_rpow ?_ hp)).trans ha⟩
    · intro i hi
      refine ⟨(hT i hi).1, fun hzero => ?_⟩
      have hz := (hT i hi).2
      rw [hzero, zero_mul, NNReal.coe_zero, norm_le_zero_iff] at hz
      exact hz
    · by_cases hz : ω i = 0
      · simp only [hz, div_zero, zero_le]
      · exact (div_le_iff₀ (pos_iff_ne_zero.mpr hz)).mpr (by simpa only [mul_comm] using hb i hi)
  · rintro ⟨hs, hb⟩
    refine ⟨(fun i => ‖T i‖₊ / ω i), hb, fun i hi => ⟨(hs i hi).1, ?_⟩⟩
    -- The proposed allocation is the actual normalized norm, so the norm bound is exact.
    by_cases hz : ω i = 0
    · simp only [(hs i hi).2 hz, norm_zero, hz, zero_mul, NNReal.coe_zero, le_refl]
    · have he : ω i * (‖T i‖₊ / ω i) = ‖T i‖₊ := mul_div_cancel₀ _ hz
      rw [he, coe_nnnorm]

/-- Box allocations have the exact sum support, attained by spending every budget.
Use: the endpoint p=∞, q=1 of the same symmetric budget theorem.
Article: main_krylov, apA:galerkin(e), independent operator budgets.
Proof: choose the all-ones allocation; componentwise order gives its optimality. -/
theorem box_allocation_support (I : Finset ι) (a : ι → ℝ≥0) :
    IsGreatest ((fun b : ι → ℝ≥0 => ∑ i ∈ I, a i * b i) '' {b | ∀ i ∈ I, b i ≤ 1})
      (∑ i ∈ I, a i) := by
  constructor
  · exact ⟨fun _ => 1, fun _ _ => le_rfl, by simp⟩
  · rintro z ⟨b, hb, rfl⟩
    exact sum_le_sum fun i hi => by simpa only [mul_one] using mul_le_mul_right (hb i hi) (a i)

/-- Simplex allocations have the exact largest-coordinate support, including an empty index set.
Use: the endpoint p=1, q=∞ spends its entire budget on an actual largest coordinate.
Article: main_krylov, apA:galerkin(e), summed operator budgets.
Proof: choose a maximizing coordinate of the finite set; the upper bound pulls
that coordinate maximum out of every nonnegative allocated summand. -/
theorem simplex_allocation_support (I : Finset ι) (a : ι → ℝ≥0) :
    IsGreatest ((fun b : ι → ℝ≥0 => ∑ i ∈ I, a i * b i) '' {b | ∑ i ∈ I, b i ≤ 1})
      (I.sup a) := by
  classical
  constructor
  · by_cases hI : I.Nonempty
    · obtain ⟨j, hj, hmax⟩ := exists_mem_eq_sup I hI a
      refine ⟨fun i => if i = j then 1 else 0, ?_, ?_⟩
      · simp [hj]
      · simp [hj, ← hmax]
    · have he : I = ∅ := not_nonempty_iff_eq_empty.mp hI
      exact ⟨0, by simp [he], by simp [he]⟩
  · rintro z ⟨b, hb, rfl⟩
    -- The maximum coefficient controls every feasible nonnegative allocation.
    calc
      _ ≤ ∑ i ∈ I, I.sup a * b i := sum_le_sum fun i hi => mul_le_mul_left (le_sup hi) _
      _ = I.sup a * ∑ i ∈ I, b i := (mul_sum _ _ _).symm
      _ ≤ I.sup a := by simpa only [mul_one] using mul_le_mul_right hb (I.sup a)

/-- Allocated box families are exactly the original independent actual operator-norm balls.
Use: p=∞ has no hidden scalar allocation restriction or zero-budget exception.
Article: main_krylov, apA:galerkin(e), max_l ‖E_l‖/ω_l≤1.
Proof: a feasible allocation is componentwise at most one; conversely choose all ones. -/
theorem symmetric_box_family_iff (I : Finset ι) (ω : ι → ℝ≥0) (T : ι → E →L[ℝ] E) :
    T ∈ symmetricBudgetFamily I ω {a | ∀ i ∈ I, a i ≤ 1} ↔
      ∀ i ∈ I, IsSelfAdjoint (T i) ∧ ‖T i‖ ≤ (ω i : ℝ) := by
  constructor
  · rintro ⟨a, ha, hT⟩ i hi
    refine ⟨(hT i hi).1, (hT i hi).2.trans ?_⟩
    exact_mod_cast (show ω i * a i ≤ ω i by simpa only [mul_one] using mul_le_mul_right (ha i hi) (ω i))
  · intro hT
    exact ⟨fun _ => 1, fun _ _ => le_rfl, fun i hi => by simpa only [mul_one] using hT i hi⟩

end
end krylov.LinearAlgebra
