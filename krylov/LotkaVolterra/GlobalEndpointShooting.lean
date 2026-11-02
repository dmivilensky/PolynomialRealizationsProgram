import krylov.LotkaVolterra.GlobalEndpointField
import krylov.LotkaVolterra.Barrier
import Mathlib.Topology.Compactness.Compact

/-!
Article: `main_krylov`, `apC:prop:g1`.

A genuine global endpoint graph is constructed by compact shooting, using
`U` instead of orbit time. The gap strip `1 ≤ e ≤ 3` is backward invariant.
Finite terminal-value problems therefore give nested nonempty compact sets
of initial gaps. Cantor intersection supplies one initial condition whose
actual solution stays in the strip for all `U ≥ 1`.

Source: the elementary compact shooting argument for a scalar ODE, with
Picard--Lindelöf, Grönwall, and Cantor intersection imported from mathlib.
No separating curve, stable manifold, or maximal-flow axiom is assumed.
-/

/-!
Article: krylov, Proposition D.12 [apC:prop:g1].

The genuine endpoint separating graph has its analytic extension and unbounded U trajectory.
Original-time entrance/exit sets are the two open intervals around its unique crossing.
The complement in the article is nonempty; Lean proves the stronger singleton description after
uniqueness.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal Topology

theorem exists_global_endpoint_gap_at (U₀ e₀ : ℝ) :
    ∃ e : ℝ → ℝ, e U₀ = e₀ ∧
      ∀ U, HasDerivAt e (clippedEndpointGraphRate U (e U)) U :=
  exists_global_solution_at_of_bounded_lipschitz (L := 6) (K := 3)
    clippedEndpointGraphRate_lipschitz clippedEndpointGraphRate_continuous_time
    clippedEndpointGraphRate_norm_le U₀ e₀

/-- Chosen global flow of the bounded extension, based at physical `U = 1`. -/
def endpointGapFlow (ξ : ℝ) : ℝ → ℝ :=
  (exists_global_endpoint_gap_at 1 ξ).choose

theorem endpointGapFlow_initial (ξ : ℝ) : endpointGapFlow ξ 1 = ξ :=
  (exists_global_endpoint_gap_at 1 ξ).choose_spec.1

theorem endpointGapFlow_hasDerivAt (ξ U : ℝ) :
    HasDerivAt (endpointGapFlow ξ)
      (clippedEndpointGraphRate U (endpointGapFlow ξ U)) U :=
  (exists_global_endpoint_gap_at 1 ξ).choose_spec.2 U

theorem endpointGapFlow_unique {e : ℝ → ℝ} {ξ : ℝ}
    (he : ∀ U, HasDerivAt e (clippedEndpointGraphRate U (e U)) U)
    (he₁ : e 1 = ξ) : e = endpointGapFlow ξ := by
  apply ODE_solution_unique_univ (v := clippedEndpointGraphRate)
    (s := fun _ ↦ univ) (t₀ := 1)
    (fun U ↦ (clippedEndpointGraphRate_lipschitz U).lipschitzOnWith)
    (fun U ↦ ⟨he U, mem_univ _⟩)
    (fun U ↦ ⟨endpointGapFlow_hasDerivAt ξ U, mem_univ _⟩)
  exact he₁.trans (endpointGapFlow_initial ξ).symm

/-- Grönwall gives continuous dependence on the shooting parameter on any
finite positive `U` interval. -/
theorem endpointGapFlow_lipschitz_initial {U : ℝ} (hU : 1 ≤ U) :
    LipschitzWith (Real.toNNReal (Real.exp (3 * (U - 1))))
      (fun ξ ↦ endpointGapFlow ξ U) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro ξ η
  have h := dist_le_of_trajectories_ODE clippedEndpointGraphRate_lipschitz
    (HasDerivAt.continuousOn fun t _ ↦ endpointGapFlow_hasDerivAt ξ t)
    (fun t _ ↦ (endpointGapFlow_hasDerivAt ξ t).hasDerivWithinAt)
    (HasDerivAt.continuousOn fun t _ ↦ endpointGapFlow_hasDerivAt η t)
    (fun t _ ↦ (endpointGapFlow_hasDerivAt η t).hasDerivWithinAt)
    (show dist (endpointGapFlow ξ 1) (endpointGapFlow η 1) ≤ dist ξ η by
      rw [endpointGapFlow_initial, endpointGapFlow_initial]) U ⟨hU, le_rfl⟩
  simpa [Real.coe_toNNReal, max_eq_left (Real.exp_pos _).le, mul_comm] using h

/-- Solving backward from an interior terminal gap stays strictly inside
the physical strip on each existing finite interval. -/
theorem endpoint_gap_terminal_strip {T U : ℝ} {e : ℝ → ℝ}
    (he : ∀ V, HasDerivAt e (clippedEndpointGraphRate V (e V)) V)
    (heT : e T = 2) (hU : 1 ≤ U) (hUT : U ≤ T) :
    e U ∈ Ioo (1 : ℝ) 3 := by
  have hab : 0 ≤ T - U := sub_nonneg.mpr hUT
  have hV (t : ℝ) (ht : t ∈ Icc 0 (T - U)) : 1 ≤ T - t := by linarith [ht.2]
  have hf (t : ℝ) : HasDerivAt (fun t ↦ e (T - t) - 1)
      (-clippedEndpointGraphRate (T - t) (e (T - t))) t := by
    simpa using ((he (T - t)).comp t ((hasDerivAt_id t).const_sub T)).sub_const 1
  have hg (t : ℝ) : HasDerivAt (fun t ↦ 3 - e (T - t))
      (clippedEndpointGraphRate (T - t) (e (T - t))) t := by
    simpa using ((he (T - t)).comp t ((hasDerivAt_id t).const_sub T)).const_sub 3
  have hb := pair_positive_invariant hab (fun t _ ↦ hf t) (fun t _ ↦ hg t)
    (show 0 < e (T - 0) - 1 by rw [sub_zero, heT]; norm_num)
    (show 0 < 3 - e (T - 0) by rw [sub_zero, heT]; norm_num)
    (fun t ht heq _ ↦ ?_) (fun t ht heq _ ↦ ?_)
  · change 1 < e U ∧ e U < 3
    have hid : T - (T - U) = U := by ring
    rw [hid] at hb
    constructor <;> linarith [hb.1, hb.2]
  · have heq' : e (T - t) = 1 := by linarith
    rw [heq', clippedEndpointGraphRate_eq (hV t ht)
      (show (1 : ℝ) ∈ Icc (1 : ℝ) 3 by constructor <;> norm_num)]
    norm_num [endpointGraphRate]
  · have heq' : e (T - t) = 3 := by linarith
    rw [heq', clippedEndpointGraphRate_eq (hV t ht)
      (show (3 : ℝ) ∈ Icc (1 : ℝ) 3 by constructor <;> norm_num)]
    norm_num [endpointGraphRate]
    linarith [hV t ht]

/-- Compact admissible shooting parameters up to the finite horizon `n+1`. -/
def endpointShootingSet (n : ℕ) : Set ℝ :=
  Icc 1 3 ∩ {ξ | ∀ U ∈ Icc (1 : ℝ) (n + 1), endpointGapFlow ξ U ∈ Icc (1 : ℝ) 3}

theorem endpointShootingSet_closed (n : ℕ) : IsClosed (endpointShootingSet n) := by
  unfold endpointShootingSet
  apply isClosed_Icc.inter
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro U
  apply isClosed_iInter
  intro hU
  exact isClosed_Icc.preimage (endpointGapFlow_lipschitz_initial hU.1).continuous

theorem endpointShootingSet_nonempty (n : ℕ) : (endpointShootingSet n).Nonempty := by
  obtain ⟨e, heT, he⟩ := exists_global_endpoint_gap_at (n + 1) 2
  have hstrip (U : ℝ) (hU : U ∈ Icc (1 : ℝ) (n + 1)) : e U ∈ Ioo (1 : ℝ) 3 :=
    endpoint_gap_terminal_strip he heT hU.1 hU.2
  have h₁ : (1 : ℝ) ∈ Icc (1 : ℝ) (n + 1) :=
    ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) n]⟩
  refine ⟨e 1, ⟨(hstrip 1 h₁).1.le, (hstrip 1 h₁).2.le⟩, fun U hU ↦ ?_⟩
  rw [← endpointGapFlow_unique he rfl]
  exact ⟨(hstrip U hU).1.le, (hstrip U hU).2.le⟩

theorem endpointShootingSet_antitone : Antitone endpointShootingSet := by
  intro m n hmn ξ hξ
  refine ⟨hξ.1, fun U hU ↦ hξ.2 U ⟨hU.1, ?_⟩⟩
  exact hU.2.trans (by exact_mod_cast Nat.add_le_add_right hmn 1)

/-- The central global shooting existence theorem. The result concerns an
actual solution of the unclipped endpoint equation for all `U ≥ 1`. -/
theorem exists_global_endpoint_graph_gap :
    ∃ e : ℝ → ℝ, ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧
      HasDerivAt e (endpointGraphRate U (e U)) U := by
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    endpointShootingSet (fun n ↦ endpointShootingSet_antitone (Nat.le_succ n))
    endpointShootingSet_nonempty
    (isCompact_Icc.of_isClosed_subset (endpointShootingSet_closed 0) fun _ h ↦ h.1)
    endpointShootingSet_closed
  refine ⟨endpointGapFlow ξ, fun U hU ↦ ?_⟩
  have hN : U ≤ (⌈U⌉₊ : ℕ) + (1 : ℝ) := by linarith [Nat.le_ceil U]
  have hmem := (mem_iInter.mp hξ ⌈U⌉₊).2 U ⟨hU, hN⟩
  refine ⟨hmem, ?_⟩
  simpa only [clippedEndpointGraphRate_eq hU hmem] using endpointGapFlow_hasDerivAt ξ U

end
end krylov.LotkaVolterra
