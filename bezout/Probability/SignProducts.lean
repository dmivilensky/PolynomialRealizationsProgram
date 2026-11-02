import bezout.Probability.Signs
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: bezout, Appendix D, orthogonality of finite channel-sign products.
Use: an actual product probability law gives the exact mean and Parseval
identity for the multilinear expansion of a perturbed oracle execution.
Proof: integrate independent Boolean coordinates; every unmatched centered
sign removes its monomial. No small-noise approximation is made.
-/

namespace bezout.Probability.SignProducts
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {N : ℕ}

/-- The independent fair sign associated with one actual oracle call. -/
def sign (s : Fin N) : (Fin N → Bool) → ℝ := Signs.error 1 s

/-- The Walsh monomial of a finite set of oracle times. -/
def character (I : Finset (Fin N)) (ω : Fin N → Bool) : ℝ := ∏ s ∈ I, sign s ω

/-- Empty channel products are exactly the constant nominal term. -/
@[simp] theorem character_empty (ω : Fin N → Bool) : character ∅ ω = 1 := by
  simp [character]

/-- A Boolean sign has square one at every outcome. -/
@[simp] theorem sign_sq (s : Fin N) (ω : Fin N → Bool) : sign s ω ^ 2 = 1 := by
  simpa only [sign, Real.norm_eq_abs, sq_abs, one_pow] using Signs.error_norm_sq 1 s ω

/-- The product over a mask is a product over all coordinates with inactive factors one. -/
theorem character_full_product (I : Finset (Fin N)) (ω : Fin N → Bool) :
    character I ω = ∏ s : Fin N, if s ∈ I then sign s ω else 1 := by
  rw [Finset.prod_ite_mem]
  simp only [Finset.univ_inter, character]

/-- Every real function on this finite probability space is integrable. -/
theorem integrable_scalar (f : (Fin N → Bool) → ℝ) : Integrable f (Signs.law N) := by
  fun_prop

/-- Distinct sign products are orthogonal, and each has squared L2 norm one. -/
theorem integral_character_mul (I J : Finset (Fin N)) :
    (∫ ω, character I ω * character J ω ∂Signs.law N) = if I = J then 1 else 0 := by
  let g (s : Fin N) (b : Bool) : ℝ :=
    (if s ∈ I then Signs.value 1 b else 1) * (if s ∈ J then Signs.value 1 b else 1)
  have hprod (ω : Fin N → Bool) : character I ω * character J ω = ∏ s, g s (ω s) := by
    rw [character_full_product, character_full_product, ← Finset.prod_mul_distrib]
    rfl
  have hi : iIndepFun (fun s (ω : Fin N → Bool) => g s (ω s)) (Signs.law N) :=
    iIndepFun_pi (fun s => (measurable_of_finite (g s)).aemeasurable)
  have hfactor (s : Fin N) :
      (∫ ω, g s (ω s) ∂Signs.law N) = if (s ∈ I ↔ s ∈ J) then 1 else 0 := by
    by_cases hI : s ∈ I <;> by_cases hJ : s ∈ J
    · have heq : (fun ω : Fin N → Bool => g s (ω s)) = fun _ => (1 : ℝ) := by
        funext ω
        simpa only [g, hI, hJ, ite_true, sign, Signs.error, pow_two] using sign_sq s ω
      rw [heq]
      simp only [hI, hJ, iff_self, ite_true, integral_const, probReal_univ, one_smul]
    · simpa only [g, hI, hJ, ite_true, ite_false, mul_one, iff_false, not_true_eq_false, Signs.error]
        using Signs.error_integral 1 s
    · simpa only [g, hI, hJ, ite_true, ite_false, one_mul, false_iff, not_true_eq_false, Signs.error]
        using Signs.error_integral 1 s
    · simp only [g, hI, hJ, ite_false, one_mul, iff_self, ite_true, integral_const,
        probReal_univ, one_smul]
  simp_rw [hprod]
  rw [hi.integral_fun_prod_eq_prod_integral (fun s =>
    (measurable_of_finite (fun ω : Fin N → Bool => g s (ω s))).stronglyMeasurable.aestronglyMeasurable)]
  simp_rw [hfactor]
  by_cases hIJ : I = J
  · subst J
    simp
  · rw [ite_eq_right hIJ]
    have hd : ∃ s, ¬(s ∈ I ↔ s ∈ J) := by
      by_contra hn
      push Not at hn
      exact hIJ (Finset.ext hn)
    obtain ⟨s, hs⟩ := hd
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

/-- A nonempty product of independent centered signs has zero mean. -/
theorem integral_character (I : Finset (Fin N)) :
    (∫ ω, character I ω ∂Signs.law N) = if I = ∅ then 1 else 0 := by
  simpa only [character_empty, mul_one] using integral_character_mul I ∅

/-- Natural-time monomials match the indexing of the finite insertion expansion. -/
def characterNat (N : ℕ) (I : Finset ℕ) (ω : Fin N → Bool) : ℝ :=
  ∏ s ∈ I, Signs.stream N 1 s ω

/-- Restrict a natural-time mask to its actual finite call indices. -/
def indexSet (N : ℕ) (I : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun s => s.val ∈ I)

/-- A bounded natural-time monomial is exactly its finite-coordinate character. -/
theorem characterNat_eq (I : Finset ℕ) (hI : I ⊆ Finset.range N) (ω : Fin N → Bool) :
    characterNat N I ω = character (indexSet N I) ω := by
  rw [character_full_product]
  have hp := Finset.prod_ite_mem (Finset.range N) I (fun s => Signs.stream N 1 s ω)
  rw [Finset.inter_eq_right.mpr hI] at hp
  rw [characterNat, ← hp, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro s _
  simp only [indexSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Signs.stream, s.isLt, dite_true, sign]

/-- Bounded natural masks are determined by their finite-coordinate indices. -/
theorem indexSet_eq_iff (I J : Finset ℕ) (hI : I ⊆ Finset.range N)
    (hJ : J ⊆ Finset.range N) : indexSet N I = indexSet N J ↔ I = J := by
  constructor
  · intro he
    apply Finset.ext
    intro s
    by_cases hs : s < N
    · have ht := congrArg (fun S : Finset (Fin N) => (⟨s, hs⟩ : Fin N) ∈ S) he
      apply iff_of_eq
      simpa only [indexSet, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    · have hi : s ∉ I := fun h => hs (Finset.mem_range.mp (hI h))
      have hj : s ∉ J := fun h => hs (Finset.mem_range.mp (hJ h))
      simp only [hi, hj]
  · rintro rfl
    rfl

/-- Exact orthogonality in the natural-time insertion indexing. -/
theorem integral_characterNat_mul (I J : Finset ℕ) (hI : I ⊆ Finset.range N)
    (hJ : J ⊆ Finset.range N) :
    (∫ ω, characterNat N I ω * characterNat N J ω ∂Signs.law N) =
      if I = J then 1 else 0 := by
  simp_rw [characterNat_eq I hI, characterNat_eq J hJ]
  rw [integral_character_mul]
  simp only [indexSet_eq_iff I J hI hJ]

/-- The actual natural-time sign monomial has the required nominal mean. -/
theorem integral_characterNat (I : Finset ℕ) (hI : I ⊆ Finset.range N) :
    (∫ ω, characterNat N I ω ∂Signs.law N) = if I = ∅ then 1 else 0 := by
  simpa only [characterNat, Finset.prod_empty, mul_one] using
    integral_characterNat_mul I ∅ hI (Finset.empty_subset _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The expected inner product of two Hilbert-valued monomials is diagonal. -/
theorem integral_inner_characterNat (I J : Finset ℕ) (hI : I ⊆ Finset.range N)
    (hJ : J ⊆ Finset.range N) (u v : E) :
    (∫ ω, inner ℝ (characterNat N I ω • u) (characterNat N J ω • v) ∂Signs.law N) =
      (if I = J then 1 else 0) * inner ℝ u v := by
  have he (ω : Fin N → Bool) :
      inner ℝ (characterNat N I ω • u) (characterNat N J ω • v) =
        (characterNat N I ω * characterNat N J ω) * inner ℝ u v := by
    simp only [inner_smul_left, inner_smul_right, conj_trivial]
    ring
  simp_rw [he]
  rw [integral_mul_const, integral_characterNat_mul I J hI hJ]

/-- Exact Parseval identity for any finite family of distinct insertion masks.
Use: apply it to all subsets, or to the nonempty subsets for terminal variance. -/
theorem integral_norm_sq_sum (S : Finset (Finset ℕ))
    (hS : ∀ I ∈ S, I ⊆ Finset.range N) (v : Finset ℕ → E) :
    (∫ ω, ‖∑ I ∈ S, characterNat N I ω • v I‖ ^ 2 ∂Signs.law N) =
      ∑ I ∈ S, ‖v I‖ ^ 2 := by
  have he (ω : Fin N → Bool) :
      ‖∑ I ∈ S, characterNat N I ω • v I‖ ^ 2 =
        ∑ I ∈ S, ∑ J ∈ S,
          inner ℝ (characterNat N I ω • v I) (characterNat N J ω • v J) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro I _
    rw [inner_sum]
  simp_rw [he]
  rw [integral_finsetSum S (fun _ _ => integrable_scalar _)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [integral_finsetSum S (fun _ _ => integrable_scalar _)]
  have hpair (J : Finset ℕ) (hJ : J ∈ S) :=
    integral_inner_characterNat I J (hS I hI) (hS J hJ) (v I) (v J)
  rw [Finset.sum_congr rfl hpair]
  have hp : (∑ J ∈ S, (if I = J then 1 else 0) * inner ℝ (v I) (v J)) =
      inner ℝ (v I) (v I) := by
    simp [ite_mul, hI]
  rw [hp, real_inner_self_eq_norm_sq]

variable [CompleteSpace E]

/-- The exact mean of a finite multilinear sign expansion is its empty-mask coefficient. -/
theorem integral_sum (S : Finset (Finset ℕ))
    (hS : ∀ I ∈ S, I ⊆ Finset.range N) (v : Finset ℕ → E) :
    (∫ ω, ∑ I ∈ S, characterNat N I ω • v I ∂Signs.law N) =
      if ∅ ∈ S then v ∅ else 0 := by
  rw [integral_finsetSum S (fun _ _ => by fun_prop)]
  have hi (I : Finset ℕ) (hI : I ∈ S) :
      (∫ ω, characterNat N I ω • v I ∂Signs.law N) =
        if I = ∅ then v I else 0 := by
    rw [integral_smul_const, integral_characterNat I (hS I hI)]
    split_ifs <;> simp only [one_smul, zero_smul]
  rw [Finset.sum_congr rfl hi]
  simp

end
end bezout.Probability.SignProducts
