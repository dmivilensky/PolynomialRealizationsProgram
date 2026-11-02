import jacobi.Variational.MomentExistence
import jacobi.Variational.FredholmCompactness

/-!
Article: jacobi, Proposition D.2.
Strictly subcritical Fredholm targets, with the scalar pole interpreted as
infinity, are feasible and have a finite attained infimum at an actual
nonzero symmetric decreasing density. Scalar Fatou handles concentrated
boxes even when their limiting target reaches a pole. The general radial
reduction and constructed compactness subsequence discharge the direct
method without an assumed minimizer or pole margin.
Source: nonnegative Fredholm series, narrow boxes and the direct variational method.
Use: supplies feasible Fredholm densities, including near the scalar spectral pole.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A canonical sequence of actual narrow boxes with exactly the prescribed positive mass.
Use: supplies feasible Fredholm densities, including near the scalar spectral pole.
Article: jacobi, Proposition D.2.
-/
def concentratedBox (M : ℝ) (hM : 0 < M) (n : ℕ) : Density :=
  narrowBox M (1/((n : ℝ)+1)) hM.le (by positivity)

/-- The top actual eigenvalue of the canonical concentrated boxes tends to their mass.
Use: the full scalar Fredholm term at M is approached from genuine finite-energy operators.
Article: jacobi, Proposition D.2.
Proof: squeeze between exp(-4r)M and M using the proved box estimate and the actual trace bound. -/
theorem concentratedBox_top_limit (M : ℝ) (hM : 0 < M) :
    Tendsto (fun n => observe (concentratedBox M hM n) .top) atTop (𝓝 M) := by
  -- Positivity and the exact trace provide an upper bound, while shrinking support provides the matching lower bound.
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-4))
  have ht := he.mul_const M
  simp only [mul_zero,exp_zero,one_mul] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds
  · exact fun n => narrowBox_top_lower M _ hM (by positivity)
  · intro n
    let b := concentratedBox M hM n
    let D := chebyshev2.Continuum.kernelSpectralData b.integrable b.nonneg
    have h := D.eigenvalue_summable.le_tsum 0 (fun j _ => D.eigenvalue_nonneg j)
    change observe b .top ≤ ∑' j, b.spectrum j at h
    rw [L1Source.spectrum,chebyshev2.Continuum.kernelEigenvalue_mass] at h
    change observe b .top ≤ b.mass at h
    exact h.trans_eq (narrowBox_mass _ _ _ _)

/-- All scalar Fredholm values at the prescribed mass are bounded by the concentrated boxes' limiting observation.
Use: proves feasibility also when sM reaches or exceeds one, without a logarithmic limit assumption.
Article: jacobi, Proposition D.2.
Proof: scalar lower semicontinuity gives the limiting top-eigenvalue term;
this is one nonnegative summand of each box's actual Fredholm series. -/
theorem concentratedBox_fredholm_liminf (M : ℝ) (hM : 0 < M) {s : ℝ} (hs : 0 ≤ s) :
    fredholmTerm s M ≤ liminf (fun n => (concentratedBox M hM n).fredholm s) atTop := by
  -- The infinite branch follows from the same proved scalar series as the finite branch.
  have h := fredholmTerm_le_liminf hs hM.le
    (fun n => observe (concentratedBox M hM n) .top)
    (fun n => (chebyshev2.Continuum.kernelSpectralData
      (concentratedBox M hM n).integrable (concentratedBox M hM n).nonneg).eigenvalue_nonneg 0)
    (concentratedBox_top_limit M hM)
  apply h.trans
  exact liminf_le_liminf (Eventually.of_forall fun n =>
    ENNReal.le_tsum (f := fun j => fredholmTerm s ((concentratedBox M hM n).spectrum j)) 0)

/-- Every target strictly below the full scalar Fredholm value at M is feasible for an actual density.
Use: discharges nonemptiness in the full Fredholm minimizer existence theorem.
Article: jacobi, Proposition D.2.
Proof: the concentrated boxes' Fredholm liminf is at least f_s(M), so some
actual box exceeds the strict target and has exactly mass M. -/
theorem fredholm_feasible {M s : ℝ} (hM : 0 < M) (hs : 0 ≤ s)
    {d : ℝ≥0∞} (hd : d < fredholmTerm s M) :
    ∃ m : Density, m.mass ≤ M ∧ d ≤ m.fredholm s := by
  have he := eventually_lt_of_lt_liminf (hd.trans_le (concentratedBox_fredholm_liminf M hM hs))
  obtain ⟨n,hn⟩ := he.exists
  exact ⟨concentratedBox M hM n,(narrowBox_mass _ _ _ _).le,hn.le⟩

/-- A positive actual extended Fredholm observation forces strictly positive mass.
Use: the Fredholm minimizer is nonzero under the article's positive target hypothesis.
Article: jacobi, Proposition D.2.
Proof: if mass vanished, every nonnegative spectral summand would vanish,
and the literal regularized Fredholm series would equal zero. -/
theorem mass_pos_of_fredholm_pos (m : Density) {s : ℝ} (hm : 0 < m.fredholm s) : 0 < m.mass := by
  -- Zero trace of the actual positive spectrum excludes all nonzero eigenvalues.
  by_contra hn
  have hz : m.mass=0 := le_antisymm (not_lt.mp hn) (integral_nonneg m.nonneg)
  let D := chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg
  have he (j : ℕ) : m.spectrum j=0 := by
    apply le_antisymm
    · have h := D.eigenvalue_summable.le_tsum j (fun k _ => D.eigenvalue_nonneg k)
      change m.spectrum j ≤ ∑' k, m.spectrum k at h
      rw [L1Source.spectrum,chebyshev2.Continuum.kernelEigenvalue_mass] at h
      change m.spectrum j ≤ m.mass at h
      rwa [hz] at h
    · exact D.eigenvalue_nonneg j
  have hzero : m.fredholm s=0 := by
    change (∑' j, fredholmTerm s (m.spectrum j))=0
    simp only [he,fredholmTerm,fredholmLog,mul_zero,not_le.mpr (by norm_num : (0 : ℝ)<1),
      ite_false,sub_zero,log_one,neg_zero,ENNReal.ofReal_zero,tsum_zero]
  rw [hzero] at hm
  exact (lt_irrefl 0) hm

/-- The full Fredholm relaxation has a finite actual radial nonzero minimizer at every positive strictly subcritical target.
Use: supplies the attained variational problem underlying the Fredholm calibration in both sources.
Article: jacobi, Proposition D.2.
Proof: concentrated boxes establish feasibility; choose costs approaching the
actual infimum and apply the proved common radial reduction. The constructed
compactness subsequence preserves the extended Fredholm constraint by upper
semicontinuity; Fatou and infimum minimality give exact attainment. -/
theorem fredholm_minimizer_exists {M s : ℝ} (hM : 0 < M) (hs : 0 < s)
    {d : ℝ≥0∞} (hd0 : 0 < d) (hd : d < fredholmTerm s M) :
    ∃ q : Density, SymmetricDecreasing q.value ∧ 0 < q.mass ∧ q.mass ≤ M ∧
      d ≤ q.fredholm s ∧ q.cost=fredholmInfimum s M d := by
  -- The actual admissible image, rather than a surrogate certificate set, defines the minimizing sequence.
  let A := Density.cost '' {m : Density | m.mass ≤ M ∧ d ≤ m.fredholm s}
  obtain ⟨w,hwM,hwd⟩ := fredholm_feasible hM hs.le hd
  have hA : A.Nonempty := ⟨w.cost,w,⟨hwM,hwd⟩,rfl⟩
  obtain ⟨u,huanti,hu,humem⟩ := exists_seq_tendsto_sInf hA (OrderBot.bddBelow A)
  choose m hm hc using humem
  choose b hbs hbM hbE hbO hbF using fun n => jacobi.Rearrangement.exists_radial_replacement (m n)
  have hu0 : u 0 ≠ ∞ := by rw [← hc 0]; exact ENNReal.ofReal_ne_top
  have hE (n : ℕ) : (b n).energy ≤ (u 0).toReal := by
    apply (hbE n).trans
    rw [← (m n).cost_toReal,hc n]
    exact ENNReal.toReal_mono hu0 (huanti (Nat.zero_le n))
  have hM' (n : ℕ) : (b n).mass ≤ M := (hbM n).trans (hm n).1
  have hd' (n : ℕ) : d ≤ (b n).fredholm s := ((hm n).2).trans (hbF n s hs.le)
  -- One selected actual density inherits the determinant constraint, even if its observation is infinite.
  obtain ⟨φ,hφ,q,hqs,hqM,hqE,hcost,hroot,hobs,hFred⟩ :=
    compact_subsequence_with_fredholm b hbs hM' hE
  have hqd : d ≤ q.fredholm s :=
    (le_liminf_of_le (h := Eventually.of_forall fun n => hd' (φ n))).trans
      (le_trans liminf_le_limsup (hFred s hs.le))
  have hcost' : q.cost ≤ fredholmInfimum s M d := by
    have hl : liminf (fun n => (b (φ n)).cost) atTop ≤ liminf (fun n => u (φ n)) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n => by
        rw [← hc (φ n)]
        exact ENNReal.ofReal_le_ofReal (hbE (φ n)))
    have he := (hu.comp hφ.tendsto_atTop).liminf_eq
    simp only [Function.comp_def] at he
    rw [he] at hl
    exact hcost.trans hl
  have hmin : fredholmInfimum s M d ≤ q.cost := sInf_le ⟨q,⟨hqM,hqd⟩,rfl⟩
  exact ⟨q,hqs,mass_pos_of_fredholm_pos q (hd0.trans_le hqd),hqM,hqd,le_antisymm hcost' hmin⟩

end
end jacobi.Variational
