import krylov.Design.OptimizerSupport
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: main_krylov, thm:B, at most M+1 support points.
Use: obtain the sharp support-size bound directly from the polynomial
equivalence certificate. Every interior contact of a one-signed real
polynomial is a double root; the two endpoints need only be simple.
Source: the classical polynomial-design support argument, using mathlib's
Fermat theorem, root multiplicities, and polynomial root-count bound.
-/

/-!
Article: krylov, Theorem D.1 [thm:B].

Attainment and the sharp support size are on all probability measures. The exact maximum-
sensitivity equivalence, support equality and tangent upper certificate have the printed
factors.
Lean Fin M indexes degrees i+1. Positive last weight rules out the zero objective; the cardinal
hypothesis derives positive moment matrices rather than assuming their inverses exist.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Matrix Set
open scoped BigOperators

/-- A nonpositive degree-2M polynomial has at most M+1 distinct roots in an interval.
Article: main_krylov, thm:B, sharp certificate support count.
Proof: count each interior root twice by Fermat's theorem and retain the two possible endpoint roots once. -/
theorem nonpositive_polynomial_root_card_le (P : ℝ[X]) (hP : P ≠ 0) (M : ℕ)
    (hdeg : P.natDegree ≤ 2 * M) (a b : ℝ)
    (hnonpos : ∀ x ∈ Icc a b, P.eval x ≤ 0) (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Icc a b) (hroot : ∀ x ∈ s, P.IsRoot x) : s.card ≤ M + 1 := by
  let u := (s.erase a).erase b
  have hdouble (x : ℝ) (hx : x ∈ u) : 2 ≤ P.roots.count x := by
    have hxb := (Finset.mem_erase.mp hx).1
    have hxa := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    have hxs := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
    have hxI := hs x hxs
    have hmax : IsMaxOn P.eval (Icc a b) x := by
      intro y hy
      change P.eval y ≤ P.eval x
      rw [show P.eval x = 0 from hroot x hxs]
      exact hnonpos y hy
    have hd : P.derivative.IsRoot x :=
      (hmax.isLocalMax (Icc_mem_nhds (lt_of_le_of_ne hxI.1 hxa.symm)
        (lt_of_le_of_ne hxI.2 hxb))).hasDerivAt_eq_zero (P.hasDerivAt x)
    rw [Polynomial.count_roots]
    exact Nat.succ_le_iff.mpr ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).mpr
      ⟨hroot x hxs, hd⟩)
  have hmulti : s.val + u.val ≤ P.roots := by
    apply Multiset.le_iff_count.mpr
    intro x
    by_cases hxu : x ∈ u
    · have hxs : x ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxu)
      simpa only [Multiset.count_add, Multiset.count_eq_one_of_mem s.nodup hxs,
        Multiset.count_eq_one_of_mem u.nodup hxu] using hdouble x hxu
    · by_cases hxs : x ∈ s
      · have hr : x ∈ P.roots := (Polynomial.mem_roots hP).mpr (hroot x hxs)
        have hc : 1 ≤ P.roots.count x := Nat.succ_le_iff.mpr (Multiset.count_pos.mpr hr)
        simpa only [Multiset.count_add, Multiset.count_eq_one_of_mem s.nodup hxs,
          Multiset.count_eq_zero_of_notMem hxu, add_zero] using hc
      · simp only [Multiset.count_add, Multiset.count_eq_zero_of_notMem hxs,
          Multiset.count_eq_zero_of_notMem hxu, add_zero, Nat.zero_le]
  have hc := (Multiset.card_le_card hmulti).trans ((Polynomial.card_roots' P).trans hdeg)
  have herase (t : Finset ℝ) (x : ℝ) : t.card ≤ (t.erase x).card + 1 := by
    by_cases hx : x ∈ t
    · exact (Finset.card_erase_add_one hx).ge
    · simp [hx]
  have hca := herase s a
  have hcb := herase (s.erase a) b
  simp only [Multiset.card_add, Finset.card_val] at hc
  dsimp [u] at hc
  omega

/-- The sensitivity polynomial has at most twice the largest active polynomial degree.
Article: main_krylov, thm:B. -/
theorem sensitivityPolynomial_natDegree_le (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (γ : ℝ) (ν : ProbabilityMeasure (Spectrum I))
    (p : ∀ i : Fin M, Competitor (i.val + 1) 0) :
    (sensitivityPolynomial I M w γ ν p).natDegree ≤ 2 * M := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  have hc := natDegree_C_mul_le (w i * (christoffel (i.val + 1) 0 (spectralCoordinate I) ν) ^ (γ - 1)) ((p i).val ^ 2)
  have hp := natDegree_pow_le (p := (p i).val) (n := 2)
  have hd := (p i).property.1
  exact hc.trans (hp.trans (by omega))

/-- The necessary sensitivity certificate confines a nonsingular optimizer to at most M+1 points.
Article: main_krylov, thm:B, the sharp atom bound.
Proof: every support point is a contact root of the nonpositive degree-2M
certificate gap; all interior contacts are counted twice. -/
theorem optimal_interval_support_card_le_of_positive_moments (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hG : ∀ i : Fin M, (momentGram I (i.val + 1) ν).PosDef)
    (hopt : ∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν)
    (j : Fin M) (hj : 0 < w j) : (ν : Measure (Spectrum I)).support.ncard ≤ M + 1 := by
  have hf := optimal_interval_support_finite I M w hw hγ₀ hγ₁ ν hG hopt j hj
  let p := momentCompetitors I M ν hG
  have hpos (i : Fin M) : 0 < christoffel (i.val + 1) 0 (spectralCoordinate I) ν := by
    rw [christoffel_eq_moment_inverse I _ ν (hG i)]
    exact inv_pos.mpr (hG i).inv.diag_pos
  let P := sensitivityPolynomial I M w γ ν p - C (intervalObjective I M w γ ν)
  have hP : P ≠ 0 := sensitivity_gapPolynomial_ne_zero I M w hw hγ₀ hγ₁ ν p hpos j hj
  have hdeg : P.natDegree ≤ 2 * M := by
    exact (natDegree_sub_le _ _).trans (max_le
      (sensitivityPolynomial_natDegree_le I M w γ ν p) (by simp))
  have hB := sensitivity_le_of_optimal_interval I M w hγ₀ ν hG hopt
  have heq := sensitivity_eq_on_support_of_certificate M w hw γ 0 (spectralCoordinate I)
    ν p hpos hB
  let s := hf.toFinset.image Subtype.val
  have hs (x : ℝ) (hx : x ∈ s) : x ∈ Icc I.mu I.L := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact t.property
  have hr (x : ℝ) (hx : x ∈ s) : P.IsRoot x := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have ht' : t ∈ (ν : Measure (Spectrum I)).support := hf.mem_toFinset.mp ht
    change P.eval t.val = 0
    simp only [P, eval_sub, eval_C, eval_sensitivityPolynomial]
    exact sub_eq_zero.mpr (heq t ht')
  have hn (x : ℝ) (hx : x ∈ Icc I.mu I.L) : P.eval x ≤ 0 := by
    have hb := hB (⟨x, hx⟩ : Spectrum I)
    simp only [P, eval_sub, eval_C]
    exact sub_nonpos.mpr (by simpa only [← eval_sensitivityPolynomial] using hb)
  have hc := nonpositive_polynomial_root_card_le P hP M hdeg I.mu I.L hn s hs hr
  have hcard : s.card = (ν : Measure (Spectrum I)).support.ncard := by
    rw [show s = hf.toFinset.image Subtype.val from rfl,
      Finset.card_image_of_injective _ Subtype.val_injective, ← Set.ncard_eq_toFinset_card _ hf]
  rwa [hcard] at hc

/-- Every optimizer, including singular gamma=1 optimizers, has at most M+1 actual support points.
Article: main_krylov, thm:B.
Proof: a support below the nonsingular threshold is already small; otherwise
the actual support supplies positive moments and the sharp polynomial contact count applies. -/
theorem optimal_interval_support_bound (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hopt : ∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν)
    (j : Fin M) (hj : 0 < w j) :
    (ν : Measure (Spectrum I)).support.Finite ∧ (ν : Measure (Spectrum I)).support.ncard ≤ M + 1 := by
  by_cases hc : (M + 1 : ℕ∞) ≤ (ν : Measure (Spectrum I)).support.encard
  · have hG := exists_positive_moments_of_support_card I M ν hc
    exact ⟨optimal_interval_support_finite I M w hw hγ₀ hγ₁ ν hG hopt j hj,
      optimal_interval_support_card_le_of_positive_moments I M w hw hγ₀ hγ₁ ν hG hopt j hj⟩
  · have hlt := lt_of_not_ge hc
    have hf : (ν : Measure (Spectrum I)).support.Finite :=
      Set.encard_lt_top_iff.mp (hlt.trans_le le_top)
    have hcard : (ν : Measure (Spectrum I)).support.ncard < M + 1 := by
      rw [← hf.cast_ncard_eq] at hlt
      exact_mod_cast hlt
    exact ⟨hf, hcard.le⟩

/-- The original mixed design has a genuine maximizing measure with at most M+1 atoms, for the full exponent range including gamma=1.
Article: main_krylov, thm:B, attainment with sharp support size.
Proof: actual compact-measure attainment followed by the proved sharp support theorem. -/
theorem intervalObjective_attains_small_support (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (j : Fin M) (hj : 0 < w j) :
    ∃ ν : ProbabilityMeasure (Spectrum I),
      (∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν) ∧
      (ν : Measure (Spectrum I)).support.Finite ∧ (ν : Measure (Spectrum I)).support.ncard ≤ M + 1 := by
  obtain ⟨ν, hopt⟩ := intervalObjective_attains I M w hw hγ₀.le
  exact ⟨ν, hopt, optimal_interval_support_bound I M w hw hγ₀ hγ₁ ν hopt j hj⟩

end
end krylov.Design
