import jacobi.Bessel.McMahonAlgebra

/-!
Article: jacobi, Proposition B.1.
The original canonically enumerated Bessel zeros satisfy the exact printed
correction with a uniform cubic remainder, for every alpha>-1 and every
positive source index. The proof uses actual singular Sturm comparison,
the true ordinary phase and its explicit integrable corrected invariant.
Source: McMahon's classical Bessel-zero expansion, proved here directly.
Use: gives explicit positive uniform denominators when the genuine reciprocal-zero correction is replaced by the printed leading phase.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every actual leading Bessel phase is at least pi*(k+1)/4 on the full source order range.
Use: gives explicit positive uniform denominators when the genuine reciprocal-zero correction is replaced by the printed leading phase.
Article: jacobi, Proposition B.1.
Proof: alpha/2+3/4>1/4 and the source index is nonnegative. -/
theorem phaseGrid_lower {a : ℝ} (ha : -1<a) (k : ℕ) :
    (Real.pi/4)*(k+1:ℝ)≤phaseGrid a k := by
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  unfold phaseGrid
  nlinarith [Real.pi_pos]

/-- McMahon's expansion holds for the actual original canonically indexed Bessel zeros, with the source cubic error and no asymptotic premises.
Use: supplies B2 to the uniform Jacobi two-edge estimate and to the later reference-spectrum perturbation and norming-ratio arguments.
Article: jacobi, Proposition B.1.
Proof: the proved leading inverse-index error makes the genuine zero at
least half its phase once it is large. The actual corrected-phase theorem
gives a cubic reciprocal-zero error there; the elementary replacement
lemma converts it to the explicit printed reciprocal phase. Finally sum
the finitely many initial scaled errors to obtain one uniform constant. -/
theorem mcmahon {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ k,
      |positiveZero a ha k-phaseGrid a k-(1/4-a^2)/(2*phaseGrid a k)|≤C/(k+1:ℝ)^3 := by
  -- Both asymptotic inputs below are proved for the original Bessel function; no independent phase or zero-estimate assumptions enter this theorem.
  obtain ⟨A,hA,hfirst⟩ := positiveZero_phase_bound ha
  let c : ℝ := 1/4-a^2
  let B : ℝ := (c^2+|c|)/3+|c|/4
  let d : ℝ := Real.pi/8
  have hd : 0<d := by dsimp [d]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  apply inversePower_bound_all 3 (C := B/d^3+|c| *A/(2*d^2))
  have he := (positiveZero_tendsto ha).eventually (eventually_ge_atTop (max A (2*(a^2+1))))
  filter_upwards [he] with k hk
  have hj := (positiveZero_properties ha k).1
  have hkp : 0<(k+1:ℝ) := by positivity
  have hAdiv : A/(k+1:ℝ)≤A := by
    exact div_le_self hA.le (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hdiff : |positiveZero a ha k-phaseGrid a k|≤A := (hfirst k).trans hAdiv
  have hphase : phaseGrid a k≤2*positiveZero a ha k := by
    have hh := (abs_le.mp hdiff).1
    have hhA := (le_max_left A (2*(a^2+1))).trans hk
    linarith
  have hlower : d*(k+1:ℝ)≤positiveZero a ha k := by
    have hg := phaseGrid_lower ha k
    dsimp [d]
    linarith
  have hvlower : d*(k+1:ℝ)≤phaseGrid a k := by
    have hg := phaseGrid_lower ha k
    dsimp [d]
    linarith [mul_nonneg Real.pi_pos.le hkp.le]
  exact reciprocal_correction_bound hkp hd hA.le hB hlower hvlower (hfirst k)
    (positiveZero_reciprocal_cubic ha k ((le_max_right A (2*(a^2+1))).trans hk))

end
end jacobi.Bessel
