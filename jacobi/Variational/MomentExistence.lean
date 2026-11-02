import jacobi.Rearrangement.RadialReduction
import jacobi.Variational.MomentFeasibility
import Mathlib.Topology.Order.IsLUB

/-!
Article: jacobi, Proposition D.2.
For every nonempty collection of strictly positive subcritical moment
thresholds, the actual infimum is finite and attained by a nonzero symmetric
decreasing density. Feasibility is proved using actual narrow boxes, symmetry
reduction is proved for every finite-energy density, and the compactness
subsequence is constructed. No minimizer, convergence or multiplier premise
is assumed in the final existence theorem.
Source: the direct method, using mathlib's monotone infimum approximation.
Use: the minimizer constructed from a nonempty positive constraint set is nonzero.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- A strictly positive actual moment observation forces positive mass.
Use: the minimizer constructed from a nonempty positive constraint set is nonzero.
Article: jacobi, Proposition D.2.
Proof: the top eigenvalue is at most the trace, and the second moment is at
most the top eigenvalue times the trace. Zero mass forces both observations to vanish. -/
theorem mass_pos_of_observe_pos (m : Density) (i : Observation) (hi : 0 < observe m i) :
    0 < m.mass := by
  -- The same actual spectral trace controls both choices of observation.
  let D := chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg
  have ht : observe m .top ≤ m.mass := by
    have h := D.eigenvalue_summable.le_tsum 0 (fun j _ => D.eigenvalue_nonneg j)
    change m.spectrum 0 ≤ ∑' j, m.spectrum j at h
    rwa [L1Source.spectrum,chebyshev2.Continuum.kernelEigenvalue_mass] at h
  cases i with
  | top => exact hi.trans_le ht
  | second =>
    have h := jacobi.Continuum.kernel_moment_bound m.integrable m.nonneg 1
    change observe m .second ≤ observe m .top^1*m.mass at h
    rw [pow_one] at h
    by_contra hn
    have hm0 : m.mass=0 := le_antisymm (not_lt.mp hn) (integral_nonneg m.nonneg)
    rw [hm0,mul_zero] at h
    exact (not_lt_of_ge h) hi

/-- Every strictly subcritical nonempty root-free joint moment relaxation is attained at an actual radial nonzero density.
Use: the existence theorem required by the second-moment and ground-state calibrations, including joint constraints.
Article: jacobi, Proposition D.2.
Proof: narrow boxes prove nonemptiness. Choose a decreasing sequence of costs
approaching the actual infimum, replace each density by its proved radial
improvement, and apply the proved compactness theorem. Spectral convergence
preserves constraints; Fatou and infimum minimality identify the limiting cost exactly. -/
theorem moment_minimizer_exists {M : ℝ} (hM : 0 < M)
    (S : Set Observation) (hS : S.Nonempty) (T : Observation → ℝ)
    (hT0 : ∀ i ∈ S, 0 < T i)
    (hT : ∀ i ∈ S, T i < match i with | .second => M^2 | .top => M) :
    ∃ q : Density, SymmetricDecreasing q.value ∧ 0 < q.mass ∧ q.mass ≤ M ∧
      (∀ i ∈ S, T i ≤ observe q i) ∧ q.cost=relaxedInfimum S M T := by
  -- The minimizing sequence is chosen from the actual image of admissible density costs.
  let A := Density.cost '' {m : Density | m.mass ≤ M ∧ ∀ i ∈ S, T i ≤ observe m i}
  obtain ⟨w,hwM,hwT⟩ := moment_feasible hM S T hT
  have hA : A.Nonempty := ⟨w.cost,w,⟨hwM,hwT⟩,rfl⟩
  obtain ⟨u,huanti,hu,humem⟩ := exists_seq_tendsto_sInf hA (OrderBot.bddBelow A)
  choose m hm hc using humem
  choose b hbs hbM hbE hbO using fun n => jacobi.Rearrangement.exists_radial_moment_replacement (m n)
  have hu0 : u 0 ≠ ∞ := by rw [← hc 0]; exact ENNReal.ofReal_ne_top
  have hE (n : ℕ) : (b n).energy ≤ (u 0).toReal := by
    apply (hbE n).trans
    rw [← (m n).cost_toReal,hc n]
    exact ENNReal.toReal_mono hu0 (huanti (Nat.zero_le n))
  have hM' (n : ℕ) : (b n).mass ≤ M := (hbM n).trans (hm n).1
  have hT' (n : ℕ) (i : Observation) (hi : i ∈ S) : T i ≤ observe (b n) i :=
    ((hm n).2 i hi).trans (hbO n i)
  -- Compactness constructs one limiting density and one subsequence for all active constraints.
  obtain ⟨φ,hφ,q,hqs,hqM,hqE,hpoint,hcost,hroot,hobs⟩ := compact_subsequence b hbs hM' hE
  have hqT (i : Observation) (hi : i ∈ S) : T i ≤ observe q i :=
    ge_of_tendsto (hobs i) (Eventually.of_forall fun n => hT' (φ n) i hi)
  have hcost' : q.cost ≤ relaxedInfimum S M T := by
    have hl : liminf (fun n => (b (φ n)).cost) atTop ≤ liminf (fun n => u (φ n)) atTop := by
      exact liminf_le_liminf (Eventually.of_forall fun n => by
        rw [← hc (φ n)]
        exact ENNReal.ofReal_le_ofReal (hbE (φ n)))
    have he := (hu.comp hφ.tendsto_atTop).liminf_eq
    simp only [Function.comp_def] at he
    rw [he] at hl
    exact hcost.trans hl
  have hmin : relaxedInfimum S M T ≤ q.cost := sInf_le ⟨q,⟨hqM,hqT⟩,rfl⟩
  obtain ⟨i,hi⟩ := hS
  exact ⟨q,hqs,mass_pos_of_observe_pos q i ((hT0 i hi).trans_le (hqT i hi)),hqM,hqT,
    le_antisymm hcost' hmin⟩

/-- The actual joint moment infimum is finite under precisely the article's subcritical hypotheses.
Use: the infimum is a finite attained energy in both root-free calibration regimes.
Article: jacobi, Proposition D.2.
Proof: the proved attaining density has finite energy by its actual domain. -/
theorem moment_infimum_ne_top {M : ℝ} (hM : 0 < M)
    (S : Set Observation) (hS : S.Nonempty) (T : Observation → ℝ)
    (hT0 : ∀ i ∈ S, 0 < T i)
    (hT : ∀ i ∈ S, T i < match i with | .second => M^2 | .top => M) :
    relaxedInfimum S M T ≠ ∞ := by
  obtain ⟨q,_,_,_,_,he⟩ := moment_minimizer_exists hM S hS T hT0 hT
  rw [← he]
  exact ENNReal.ofReal_ne_top

end
end jacobi.Variational
