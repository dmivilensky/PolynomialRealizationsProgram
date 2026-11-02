import krylov.Realization.BudgetConversion
import krylov.Stability.CompactCoefficients

/-!
Article: main_krylov, prop:conv, compact-uniform actual secant-budget conversion.
Use: obtain one quadratic trajectory-replacement bound on a genuine compact
reference set from primitive smoothness, including the real canonical metric.
Source: the finite observed-coordinate mean-value theorem, compact derivative
tubes and the proved exact cumulative secant injection inequality.
-/

namespace krylov.Realization
noncomputable section
open krylov.Stability Set Finset
open scoped Topology BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Actual finite smooth step and increment families have one compact-uniform first-order variation bound.
Use: replace pointwise asymptotics by a real common neighborhood, including all finite prefixes and zero horizons.
Article: main_krylov, prop:conv and lem:U.
Proof: bundle the actual finite observations in their product supremum norm.
Their genuine finite-order smooth locus is open; the compact mean-value bound
controls every true coordinate, and increments vanish at the reference. -/
theorem compact_step_increment_bounds
    (s : X → ℕ → E) (D : X → ℕ → E →L[ℝ] E) (N : ℕ) (K : Set X)
    (hK : IsCompact K)
    (hs : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => s p i) x)
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => D p i) x)
    (hzero : ∀ x∈K, ∀ i<N, D x i=0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      (∀ i<N, ‖s (x+h) i-s x i‖≤C*‖h‖) ∧ ∀ i<N, ‖D (x+h) i‖≤C*‖h‖ := by
  -- The finite product contains exactly the real steps and increments through the chosen horizon.
  let F : X → (Fin N → E) × (Fin N → E →L[ℝ] E) :=
    fun p => (fun i => s p i.val,fun i => D p i.val)
  have hf : ∀ x∈K, ContDiffAt ℝ 1 F x := fun x hx =>
    (contDiffAt_pi.mpr fun i : Fin N => hs x hx i.val i.isLt).prodMk
      (contDiffAt_pi.mpr fun i : Fin N => hD x hx i.val i.isLt)
  let U := interior {x | ContDiffAt ℝ 1 F x}
  have hsub : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hf x hx).eventually (by simp))
  obtain ⟨δ,M,hδ,hM,hLip⟩ := compact_local_lipschitz F U K isOpen_interior hK hsub
    (fun x hx => (show ContDiffAt ℝ 1 F x from interior_subset hx).contDiffWithinAt)
  refine ⟨δ,M,hδ,hM,?_⟩
  intro x hx h hh
  have hdiff : ‖F (x+h)-F x‖≤M*‖h‖ := by
    simpa only [add_sub_cancel_left] using hLip x hx (x+h) (by simpa only [add_sub_cancel_left] using hh)
  have hstep (i : ℕ) (hi : i<N) : ‖s (x+h) i-s x i‖≤M*‖h‖ :=
    (norm_le_pi_norm (F (x+h)-F x).1 ⟨i,hi⟩).trans ((norm_fst_le _).trans hdiff)
  have hop (i : ℕ) (hi : i<N) : ‖D (x+h) i‖≤M*‖h‖ := by
    have hb := (norm_le_pi_norm (F (x+h)-F x).2 ⟨i,hi⟩).trans ((norm_snd_le _).trans hdiff)
    simpa only [F,Prod.snd_sub,Pi.sub_apply,hzero x hx i hi,sub_zero] using hb
  exact ⟨hstep,hop⟩

 /-- Replacing actual smooth steps by their genuine reference steps has a compact-uniform quadratic cumulative-injection remainder.
Use: all actual finite prefixes share the same radius and constant; no trajectory error is assumed.
Article: main_krylov, prop:conv, O_K(ω²).
Proof: the common first-order step and primitive increment bounds multiply
inside the exact injection-difference inequality. Bound the number of actual
chronological pairs by the square of the finite horizon. -/
theorem compact_secantInjection_quadratic
    (s : X → ℕ → E) (D : X → ℕ → E →L[ℝ] E) (N : ℕ) (K : Set X)
    (hK : IsCompact K)
    (hs : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => s p i) x)
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => D p i) x)
    (hzero : ∀ x∈K, ∀ i<N, D x i=0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖secantInjection (D (x+h)) (s (x+h)) j-secantInjection (D (x+h)) (s x) j‖≤C*‖h‖^2 := by
  -- Primitive first derivatives give one common bound for all actual steps and increments.
  obtain ⟨δ,M,hδ,hM,hbound⟩ := compact_step_increment_bounds s D N K hK hs hD hzero
  refine ⟨δ,(N : ℝ)^2*M^2,hδ,by positivity,?_⟩
  intro x hx h hh j hj
  obtain ⟨hstep,hop⟩ := hbound x hx h hh
  apply (secantInjection_difference_le _ _ _ j).trans
  calc
    _ ≤ ∑ k∈range j, ∑ _l∈range k, M^2*‖h‖^2 := by
      apply sum_le_sum
      intro k hk
      apply sum_le_sum
      intro l hl
      have hk' : k<N := lt_of_lt_of_le (mem_range.mp hk) hj
      have hl' : l<N := lt_trans (mem_range.mp hl) hk'
      exact (mul_le_mul (hop l hl') (hstep k hk') (norm_nonneg _) (by positivity)).trans_eq (by ring)
    _ ≤ ∑ _k∈range j, (N : ℝ)*(M^2*‖h‖^2) := by
      apply sum_le_sum
      intro k hk
      simp only [sum_const,nsmul_eq_mul,card_range]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (le_trans (mem_range.mp hk).le hj)) (by positivity)
    _ ≤ (N : ℝ)*((N : ℝ)*(M^2*‖h‖^2)) := by
      simp only [sum_const,nsmul_eq_mul,card_range]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
    _ = _ := by ring

/-- The genuine reference canonical transformation preserves the compact-uniform quadratic injection replacement bound.
Use: a variable positive metric needs only proved continuity of its actual root, rather than an unnecessary differentiability assumption on that root.
Article: main_krylov, prop:conv, actual canonical secant injections.
Proof: compactness bounds the actual reference transformation. The common
primitive first-order increment and real physical step-error bounds then
multiply with this bound in each genuine chronological injection term. -/
theorem compact_canonical_secantInjection_quadratic
    (s : X → ℕ → E) (D : X → ℕ → E →L[ℝ] E) (R : X → E →L[ℝ] E)
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hs : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => s p i) x)
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => D p i) x)
    (hzero : ∀ x∈K, ∀ i<N, D x i=0) (hR : ContinuousOn R K) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖secantInjection (D (x+h)) (fun i => R x (s (x+h) i)) j-
        secantInjection (D (x+h)) (fun i => R x (s x i)) j‖≤C*‖h‖^2 := by
  -- The true canonical root is held at the reference: only its compact bound is needed.
  obtain ⟨δ,M,hδ,hM,hbound⟩ := compact_step_increment_bounds s D N K hK hs hD hzero
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hR
  refine ⟨δ,(N : ℝ)^2*M^2*|B|,hδ,by positivity,?_⟩
  intro x hx h hh j hj
  obtain ⟨hstep,hop⟩ := hbound x hx h hh
  apply (secantInjection_difference_le _ _ _ j).trans
  calc
    _ ≤ ∑ k∈range j, ∑ _l∈range k, M^2*|B| *‖h‖^2 := by
      apply sum_le_sum
      intro k hk
      apply sum_le_sum
      intro l hl
      have hk' : k<N := lt_of_lt_of_le (mem_range.mp hk) hj
      have hl' : l<N := lt_trans (mem_range.mp hl) hk'
      have hc : ‖R x (s (x+h) k)-R x (s x k)‖≤|B| *(M*‖h‖) := by
        rw [← map_sub]
        exact ((R x).le_opNorm _).trans (mul_le_mul ((hB x hx).trans (le_abs_self B))
          (hstep k hk') (norm_nonneg _) (abs_nonneg B))
      exact (mul_le_mul (hop l hl') hc (norm_nonneg _) (by positivity)).trans_eq (by ring)
    _ ≤ ∑ _k∈range j, (N : ℝ)*(M^2*|B| *‖h‖^2) := by
      apply sum_le_sum
      intro k hk
      simp only [sum_const,nsmul_eq_mul,card_range]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (le_trans (mem_range.mp hk).le hj)) (by positivity)
    _ ≤ (N : ℝ)*((N : ℝ)*(M^2*|B| *‖h‖^2)) := by
      simp only [sum_const,nsmul_eq_mul,card_range]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
    _ = _ := by ring

/-- The actual canonical cumulative-injection remainder has the printed compact-uniform positive reference-error weight.
Use: the initial canonical error norm can be used with its proved continuity and positivity.
Article: main_krylov, prop:conv and lem:U.
Proof: the genuine positive reference weight attains a positive compact
minimum. Divide the proved common canonical conversion constant by that
minimum; handle an empty compact without selecting a reference. -/
theorem compact_canonical_secantInjection_weighted
    (s : X → ℕ → E) (D : X → ℕ → E →L[ℝ] E) (R : X → E →L[ℝ] E)
    (e : X → ℝ) (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hs : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => s p i) x)
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => D p i) x)
    (hzero : ∀ x∈K, ∀ i<N, D x i=0) (hR : ContinuousOn R K)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖secantInjection (D (x+h)) (fun i => R x (s (x+h) i)) j-
        secantInjection (D (x+h)) (fun i => R x (s x i)) j‖≤C*‖h‖^2*e x := by
  -- The compact minimum belongs to the actual positive error norm on actual references.
  by_cases hn : K.Nonempty
  · obtain ⟨δ,M,hδ,hM,hrem⟩ := compact_canonical_secantInjection_quadratic s D R N K hK hs hD hzero hR
    obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hn he
    have hp := hepos x₀ hx₀
    refine ⟨δ,M/e x₀,hδ,div_nonneg hM hp.le,?_⟩
    intro x hx h hh j hj
    have hM' : M≤M/e x₀*e x := by
      calc
        M = M/e x₀*e x₀ := (div_mul_cancel₀ M hp.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmin hx) (div_nonneg hM hp.le)
    exact (hrem x hx h hh j hj).trans
      ((mul_le_mul_of_nonneg_right hM' (sq_nonneg ‖h‖)).trans_eq (by ring))
  · refine ⟨1,0,zero_lt_one,le_refl 0,?_⟩
    intro x hx
    exact (hn ⟨x,hx⟩).elim

end
end krylov.Realization
