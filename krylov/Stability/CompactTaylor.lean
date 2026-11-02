import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Article: main_krylov, lem:U(a), compact-uniform Taylor remainders.
Use: obtain one genuine perturbation neighborhood and one remainder constant
for all reference points in a compact subset of the smooth solve domain.
Source: mathlib's multidimensional integral Taylor theorem and compact
closed-thickening theorem, followed by the multilinear operator-norm bound.
-/

namespace krylov.Stability
noncomputable section
open Filter Set Metric
open scoped Topology BigOperators
variable {Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The actual finite Taylor polynomial using genuine iterated Fréchet derivatives.
Use: all compact remainder estimates refer to these actual coefficients.
Article: main_krylov, lem:U(a), Σ_(j<k)P_j. -/
def taylorPolynomial (f : Z → F) (k : ℕ) (x h : Z) : F :=
  ∑ j∈Finset.range k, (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f x (fun _ => h)

/-- A genuine derivative bound along a segment bounds its actual multidimensional Taylor remainder.
Use: the compact argument supplies the same derivative bound along every nearby reference segment.
Article: main_krylov, lem:U(a), integral Taylor remainder.
Source: mathlib map_add_eq_sum_add_integral_iteratedFDeriv.
Proof: insert the proved integral Taylor identity; its scalar kernel is at
most one on [0,1], and the actual multilinear action contributes ‖h‖^(n+1). -/
theorem taylor_remainder_bound (f : Z → F) (n : ℕ) (x h : Z) {M : ℝ}
    (hf : ∀ t∈Icc (0 : ℝ) 1, ContDiffAt ℝ (n+1) f (x+t • h))
    (hD : ∀ t∈Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n+1) f (x+t • h)‖≤M) :
    ‖f (x+h)-taylorPolynomial f (n+1) x h‖≤(n.factorial : ℝ)⁻¹*M*‖h‖^(n+1) := by
  -- The integral is bounded uniformly over the genuine segment joining x to x+h.
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv hf
  change f (x+h)=taylorPolynomial f (n+1) x h+_ at ht
  rw [ht, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hb : ‖∫ t in (0 : ℝ)..1, (1-t)^n •
      iteratedFDeriv ℝ (n+1) f (x+t • h) (fun _ => h)‖≤M*‖h‖^(n+1) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := M*‖h‖^(n+1)) (f := fun t => (1-t)^n •
        iteratedFDeriv ℝ (n+1) f (x+t • h) (fun _ => h)) (fun t ht => ?_)
    · simpa only [sub_zero, abs_one, mul_one] using hi
    · rw [uIoc_of_le zero_le_one] at ht
      have ht' : t∈Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2⟩
      have hw : ‖(1-t)^n‖≤1 := by
        rw [Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr ht'.2) _)]
        exact pow_le_one₀ (sub_nonneg.mpr ht'.2) (by linarith [ht'.1])
      have hd := (iteratedFDeriv ℝ (n+1) f (x+t • h)).le_opNorm (fun _ => h)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
      rw [norm_smul]
      exact (mul_le_mul hw (hd.trans (mul_le_mul_of_nonneg_right (hD t ht')
        (pow_nonneg (norm_nonneg _) _))) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq (by ring)

variable [ProperSpace Z]

omit [CompleteSpace F] in
/-- Every compact subset of an actual smooth open domain has one compact tube with uniformly bounded derivatives through the stated order.
Use: uniformity is proved from genuine derivatives and compactness, rather than stored as a trajectory hypothesis.
Article: main_krylov, lem:U(a), compact reference tube.
Proof: choose an actual closed thickening contained in the open domain;
each continuous genuine derivative is bounded on that compact thickening, and
a finite sum of those bounds supplies one constant for all orders. -/
theorem compact_derivative_tube (f : Z → F) (r : ℕ) (U K : Set Z) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K⊆U) (hf : ContDiffOn ℝ r f U) :
    ∃ δ M : ℝ, 0<δ ∧ 0≤M ∧ cthickening δ K⊆U ∧
      ∀ k≤r, ∀ z∈cthickening δ K, ‖iteratedFDeriv ℝ k f z‖≤M := by
  -- Compactness is used on a genuine common neighborhood, not separately at each reference point.
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hb (i : Fin (r+1)) : ∃ C : ℝ, ∀ z∈cthickening δ K, ‖iteratedFDeriv ℝ i.val f z‖≤C :=
    hK.cthickening.exists_bound_of_continuousOn
      (fun z hz => ((hf.contDiffAt (hU.mem_nhds (hδU hz))).continuousAt_iteratedFDeriv
        (by exact_mod_cast Nat.le_of_lt_succ i.isLt)).continuousWithinAt)
  choose C hC using hb
  let M := ∑ i : Fin (r+1), |C i|
  refine ⟨δ,M,hδ,Finset.sum_nonneg (fun i _ => abs_nonneg _),hδU,?_⟩
  intro k hk z hz
  have hi : (⟨k,by omega⟩ : Fin (r+1))∈(Finset.univ : Finset (Fin (r+1))) := Finset.mem_univ _
  exact ((hC ⟨k,by omega⟩ z hz).trans (le_abs_self _)).trans
    (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) hi)

/-- Actual Taylor remainders of every positive order up to r are uniformly bounded on a compact reference set.
Use: one radius and one constant work for all reference points and every perturbation direction.
Article: main_krylov, lem:U(a), full compact Taylor estimate before homogeneous normalization.
Proof: the actual compact derivative tube contains every short reference
segment; apply the integral Taylor bound at each order and use that every
reciprocal factorial is at most one. -/
theorem compact_taylor_remainders (f : Z → F) (r : ℕ) (U K : Set Z) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K⊆U) (hf : ContDiffOn ℝ r f U) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : Z, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖f (x+h)-taylorPolynomial f k x h‖≤C*‖h‖^k := by
  -- The same compact tube and actual derivative bound serve all orders and all reference segments.
  obtain ⟨δ,M,hδ,hM,hδU,hD⟩ := compact_derivative_tube f r U K hU hK hKU hf
  refine ⟨δ,M,hδ,hM,?_⟩
  intro x hx h hh k hk hkr
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hseg (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : x+t • h∈cthickening δ K := by
    apply mem_cthickening_of_dist_le (x+t • h) x δ K hx
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans (by simpa only [one_mul] using hh)
  have ht := taylor_remainder_bound f n x h
    (fun t ht => ((hf.contDiffAt (hU.mem_nhds (hδU (hseg t ht)))).of_le (by exact_mod_cast hkr)))
    (fun t ht => hD (n+1) hkr _ (hseg t ht))
  have hi : (n.factorial : ℝ)⁻¹≤1 := inv_le_one_of_one_le₀
    (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n))
  exact ht.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hM) (pow_nonneg (norm_nonneg _) _))

end
end krylov.Stability
