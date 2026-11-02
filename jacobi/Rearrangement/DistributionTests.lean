import jacobi.Rearrangement.SoftTests
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Normalized clipped tests approximate every positive strict superlevel indicator.
Their integrals therefore determine the distribution of an actual L1 density.
Layer cake then recovers mass, energy and root mass from this distribution,
including infinite root mass, without a circular tightness assumption.
Source: Lebesgue dominated convergence and Cavalieri's layer-cake formula in mathlib.
Use: pointwise approximation to the strict superlevel indicator at t.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter jacobi.Variational
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false

/-- Normalized clipped tests with transition width 1/(n+1).
Use: pointwise approximation to the strict superlevel indicator at t.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def normalizedSoft (t : ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  ((n : ℝ)+1)*softTest t (1/((n : ℝ)+1)) v

/-- Every normalized test lies between zero and one.
Use: domination by the original density divided by the positive threshold.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the clipping height cancels its positive normalizing factor exactly. -/
theorem normalizedSoft_bounds (t : ℝ) (n : ℕ) (v : ℝ) :
    0 ≤ normalizedSoft t n v ∧ normalizedSoft t n v ≤ 1 := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  obtain ⟨hl,hu⟩ := softTest_bounds t (by positivity : 0 ≤ 1/((n : ℝ)+1)) v
  refine ⟨mul_nonneg hn.le hl,?_⟩
  change ((n : ℝ)+1)*softTest t (1/((n : ℝ)+1)) v ≤ 1
  calc
    _ ≤ ((n : ℝ)+1)*(1/((n : ℝ)+1)) := mul_le_mul_of_nonneg_left hu hn.le
    _ = 1 := by field_simp

/-- Normalized tests are dominated by v/t on the nonnegative half-line.
Use: an actual L1 majorant for their full superlevel limit, independent of n.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: below t the test vanishes; above t it is at most one and one≤v/t. -/
theorem normalizedSoft_bound {t : ℝ} (ht : 0 < t) (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    normalizedSoft t n v ≤ v/t := by
  by_cases h : v ≤ t
  · rw [normalizedSoft,softTest_zero (by positivity) h,mul_zero]
    exact div_nonneg hv ht.le
  · exact (normalizedSoft_bounds t n v).2.trans ((le_div_iff₀ ht).mpr (by linarith))

/-- Normalized soft tests converge to the strict superlevel indicator at every real value.
Use: dominated convergence recovers the actual measure of {m>t}.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: below the threshold all terms vanish; above it the shrinking transition
width eventually lies below the strict value gap and the normalized test is exactly one. -/
theorem normalizedSoft_limit (t v : ℝ) :
    Tendsto (fun n => ENNReal.ofReal (normalizedSoft t n v)) atTop
      (𝓝 (if t < v then 1 else 0)) := by
  -- Eventual equality avoids any division-limit argument at a vanishing transition width.
  by_cases hv : t < v
  · have he : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (normalizedSoft t n v)=1 := by
      filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
        (gt_mem_nhds (sub_pos.mpr hv))] with n hn
      have hc : softTest t (1/((n : ℝ)+1)) v=1/((n : ℝ)+1) :=
        min_eq_right (hn.le.trans (le_max_left _ _))
      rw [normalizedSoft,hc]
      have hdiv : ((n : ℝ)+1)*(1/((n : ℝ)+1))=1 := by field_simp
      rw [hdiv,ENNReal.ofReal_one]
    simpa only [ite_eq_left hv] using tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm))
  · have he (n : ℕ) : ENNReal.ofReal (normalizedSoft t n v)=0 := by
      rw [normalizedSoft,softTest_zero (by positivity) (not_lt.mp hv),mul_zero,ENNReal.ofReal_zero]
    simpa only [he,ite_eq_right hv] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- Integrals of normalized tests converge to each actual positive superlevel measure.
Use: continuous test identities identify the whole distribution of the limiting radial density.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: dominate by ofReal(m/t), whose integral is finite by L1 membership,
and apply the proved pointwise indicator limit. -/
theorem normalizedSoft_lintegral_limit (m : L1Source) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (normalizedSoft t n (m.value x))) atTop
      (𝓝 (volume {x | t < m.value x})) := by
  -- The majorant is integrable on the entire real line, even if the density support has infinite measure.
  have hi := m.integrable.div_const t
  have hfin : (∫⁻ x, ENNReal.ofReal (m.value x/t)) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun x => div_nonneg (m.nonneg x) ht.le))]
    exact ENNReal.ofReal_ne_top
  have h := tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (m.value x/t))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_const.mul ((softTest_lipschitz _ _).continuous.measurable.comp m.measurable)))
    (fun n => Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (normalizedSoft_bound ht n (m.nonneg x)))
    hfin (Eventually.of_forall fun x => normalizedSoft_limit t (m.value x))
  have hs : MeasurableSet {x | t < m.value x} := m.measurable measurableSet_Ioi
  have he : (∫⁻ x, (if t < m.value x then (1 : ℝ≥0∞) else 0))=volume {x | t < m.value x} := by
    simpa only [Set.indicator,Pi.one_apply,mem_ofPred_eq] using lintegral_indicator_one hs
  rwa [he] at h

/-- Equal soft-test integrals imply equality of every positive strict superlevel measure.
Use: the final distribution-identification step for the actual general radial limit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: normalize the given identities, identify their real integrals with
nonnegative extended integrals, and take the two proved indicator limits. -/
theorem superlevel_eq_of_softTests (m q : L1Source)
    (h : ∀ t > 0, ∀ δ > 0, (∫ x, softTest t δ (q.value x))=∫ x, softTest t δ (m.value x))
    {t : ℝ} (ht : 0 < t) : volume {x | t < q.value x}=volume {x | t < m.value x} := by
  -- Both normalizations are finite genuine integrals before being embedded in ENNReal.
  have he (n : ℕ) : (∫⁻ x, ENNReal.ofReal (normalizedSoft t n (q.value x)))=
      ∫⁻ x, ENNReal.ofReal (normalizedSoft t n (m.value x)) := by
    have hδ : 0 < 1/((n : ℝ)+1) := by positivity
    have hq := (softTest_integrable q ht.le hδ.le).const_mul ((n : ℝ)+1)
    have hm := (softTest_integrable m ht.le hδ.le).const_mul ((n : ℝ)+1)
    unfold normalizedSoft
    rw [← ofReal_integral_eq_lintegral_ofReal hq (Eventually.of_forall (fun x => (normalizedSoft_bounds t n (q.value x)).1)),
      ← ofReal_integral_eq_lintegral_ofReal hm (Eventually.of_forall (fun x => (normalizedSoft_bounds t n (m.value x)).1))]
    congr 1
    rw [integral_const_mul,integral_const_mul,h t ht _ hδ]
  exact tendsto_nhds_unique (normalizedSoft_lintegral_limit q ht)
    ((normalizedSoft_lintegral_limit m ht).congr (fun n => (he n).symm))

/-- Equality of positive superlevel distributions determines every strict superlevel measure for nonnegative densities.
Use: completes equimeasurability at level zero, where the support may have infinite measure.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the positive support is the increasing union of levels 1/(n+1);
negative levels are the whole line. Continuity of measures from below handles level zero. -/
theorem all_superlevels_eq_of_positive (m q : L1Source)
    (h : ∀ t > 0, volume {x | t < q.value x}=volume {x | t < m.value x}) (t : ℝ) :
    volume {x | t < q.value x}=volume {x | t < m.value x} := by
  -- The countable increasing union remains valid when the measure of the positive support is infinite.
  by_cases ht : 0 < t
  · exact h t ht
  by_cases hz : t=0
  · subst t
    have he (p : L1Source) : {x | 0 < p.value x}=⋃ n : ℕ, {x | 1/((n : ℝ)+1) < p.value x} := by
      ext x
      constructor
      · intro hx
        obtain ⟨n,hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
          (gt_mem_nhds (show 0 < p.value x from hx))).exists
        exact mem_iUnion.mpr ⟨n,hn⟩
      · intro hx
        obtain ⟨n,hn⟩ := mem_iUnion.mp hx
        exact (by positivity : 0 < 1/((n : ℝ)+1)).trans hn
    have hmono (p : L1Source) : Monotone (fun n : ℕ => {x | 1/((n : ℝ)+1) < p.value x}) := by
      intro i j hij x hx
      have hd : (i : ℝ)+1 ≤ (j : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hij 1
      exact (one_div_le_one_div_of_le (by positivity) hd).trans_lt hx
    rw [he q,he m,(hmono q).measure_iUnion,(hmono m).measure_iUnion]
    exact iSup_congr fun n => h _ (by positivity)
  · have hn : t < 0 := lt_of_le_of_ne (not_lt.mp ht) hz
    have he (p : L1Source) : {x | t < p.value x}=univ := by
      ext x
      simp only [mem_ofPred_eq,mem_univ,iff_true]
      exact hn.trans_le (p.nonneg x)
    rw [he q,he m]

/-- Equal positive superlevel distributions preserve every positive power integral, even an infinite one.
Use: exact mass, energy and root-mass preservation in the general rearrangement theorem.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: mathlib's layer-cake power formula expresses the integral solely through
the positive superlevel measures; their equality identifies the entire extended integral. -/
theorem power_integral_eq_of_superlevels (m q : L1Source)
    (h : ∀ t > 0, volume {x | t < q.value x}=volume {x | t < m.value x})
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (q.value x^p))=∫⁻ x, ENNReal.ofReal (m.value x^p) := by
  -- Layer cake is applied before assuming finiteness of the power integral.
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume (Eventually.of_forall q.nonneg) q.measurable.aemeasurable hp,
    lintegral_rpow_eq_lintegral_meas_lt_mul volume (Eventually.of_forall m.nonneg) m.measurable.aemeasurable hp]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [h t ht]

/-- The three actual normalizations agree for densities with the same positive superlevel distribution.
Use: the general rearrangement preserves the exact mass equality and extended root constraint in Transfer.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: specialize layer cake to exponents 1, 3/2 and 1/2; integrability converts
the first two identities back to real integrals, while the root mass remains extended. -/
theorem integrals_eq_of_superlevels (m q : Density)
    (h : ∀ t > 0, volume {x | t < q.value x}=volume {x | t < m.value x}) :
    q.mass=m.mass ∧ q.energy=m.energy ∧ q.rootMass=m.rootMass := by
  -- The root identity includes infinity and therefore does not rely on a pre-existing root-mass bound.
  have hm := power_integral_eq_of_superlevels m q h (p := 1) (by norm_num)
  simp only [Real.rpow_one] at hm
  rw [← ofReal_integral_eq_lintegral_ofReal q.integrable (Eventually.of_forall q.nonneg),
    ← ofReal_integral_eq_lintegral_ofReal m.integrable (Eventually.of_forall m.nonneg)] at hm
  have he := power_integral_eq_of_superlevels m q h (p := 3/2) (by norm_num)
  rw [← q.cost_eq_lintegral,← m.cost_eq_lintegral] at he
  refine ⟨?_,?_,?_⟩
  · have ht := congrArg ENNReal.toReal hm
    change (∫ x, q.value x)=∫ x, m.value x
    simpa only [ENNReal.toReal_ofReal (integral_nonneg q.nonneg),
      ENNReal.toReal_ofReal (integral_nonneg m.nonneg)] using ht
  · have ht := congrArg ENNReal.toReal he
    simpa only [Density.cost_toReal] using ht
  · change (∫⁻ x, ENNReal.ofReal (sqrt (q.value x)))=∫⁻ x, ENNReal.ofReal (sqrt (m.value x))
    simp_rw [Real.sqrt_eq_rpow]
    exact power_integral_eq_of_superlevels m q h (by norm_num)

end
end jacobi.Rearrangement
