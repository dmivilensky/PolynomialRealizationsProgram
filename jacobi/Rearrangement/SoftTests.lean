import jacobi.Rearrangement.EnergyApproximation
import jacobi.Variational.Tails

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Clipped positive-part tests vanish below a positive density level. They are
nonexpansive, so their integrals respect L1 approximation. On a mass-bounded
radial family each test also has a common compact spatial support; dominated
convergence therefore applies to the selected radial limit. These two limits
identify the density distribution before recovering exact normalizations.
Source: continuous approximations to superlevel indicators and dominated convergence.
Use: identifies the distribution of the general radial limit without a priori mass tightness.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter jacobi.Variational
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false

/-- A continuous clipped test of values lying above the density level t.
Use: identifies the distribution of the general radial limit without a priori mass tightness.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def softTest (t δ v : ℝ) : ℝ := min (max (v-t) 0) δ

/-- Clipped positive-part tests are globally nonexpansive.
Use: their integral error is controlled by the actual L1 density error.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: translation is an isometry and clipping to either constant endpoint is nonexpansive. -/
theorem softTest_lipschitz (t δ : ℝ) : LipschitzWith 1 (softTest t δ) := by
  have ht : LipschitzWith 1 (fun v : ℝ => v-t) := by
    apply LipschitzWith.mk_one
    intro v w
    rw [Real.dist_eq,Real.dist_eq,show (v-t)-(w-t)=v-w by ring]
  exact (ht.max_const 0).min_const δ

/-- A soft test lies between zero and its clipping height.
Use: the common compact spatial support then supplies an integrable dominating function.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: both arguments of the outer minimum are nonnegative. -/
theorem softTest_bounds (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ) :
    0 ≤ softTest t δ v ∧ softTest t δ v ≤ δ :=
  ⟨le_min (le_max_right _ _) hδ,min_le_right _ _⟩

/-- The soft test vanishes at values below its threshold.
Use: radial mass bounds turn a value threshold into a common finite spatial support.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the positive part of v-t is zero when v≤t. -/
theorem softTest_zero {t δ v : ℝ} (hδ : 0 ≤ δ) (hv : v ≤ t) : softTest t δ v=0 := by
  rw [softTest,max_eq_right (sub_nonpos.mpr hv),min_eq_left hδ]

/-- A positive-threshold soft test is bounded by the nonnegative density value.
Use: it is integrable on every actual density, without support or boundedness assumptions.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: its positive part is at most v and the outer clipping can only decrease it. -/
theorem softTest_le_value {t : ℝ} (ht : 0 ≤ t) (δ : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    softTest t δ v ≤ v :=
  (min_le_left _ _).trans (max_le (sub_le_self _ ht) hv)

/-- Every soft test of an actual nonnegative density is absolutely integrable.
Use: all compared distribution tests are genuine real integrals.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: bound the nonnegative test by the original integrable density. -/
theorem softTest_integrable (m : L1Source) {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    Integrable (fun x => softTest t δ (m.value x)) := by
  apply m.integrable.mono'
    ((softTest_lipschitz t δ).continuous.measurable.comp m.measurable).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change |softTest t δ (m.value x)| ≤ m.value x
    rw [abs_of_nonneg (softTest_bounds t hδ _).1]
    exact softTest_le_value ht δ (m.nonneg x)

/-- Actual L1 convergence of densities preserves each soft-test integral.
Use: identifies the limit of distribution tests along the original regular approximants.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the absolute integral difference is bounded by the integral of the
pointwise test difference, then by the L1 density difference. -/
theorem softTest_integral_limit_l1 (m : ℕ → Density) (q : L1Source)
    (hl : Tendsto (fun n => ∫ x, |(m n).value x-q.value x|) atTop (𝓝 0))
    {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    Tendsto (fun n => ∫ x, softTest t δ ((m n).value x)) atTop
      (𝓝 (∫ x, softTest t δ (q.value x))) := by
  -- The global nonexpansive estimate makes support bounds unnecessary on the original side.
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hl
  intro n
  rw [Real.norm_eq_abs]
  apply (integral_distance (softTest_integrable (m n) ht hδ) (softTest_integrable q ht hδ)).trans
  apply integral_mono ((softTest_integrable (m n) ht hδ).sub (softTest_integrable q ht hδ)).abs
    ((m n).integrable.sub q.integrable).abs
  intro x
  change |softTest t δ ((m n).value x)-softTest t δ (q.value x)| ≤ |(m n).value x-q.value x|
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using
    (softTest_lipschitz t δ).dist_le_mul ((m n).value x) (q.value x)

/-- Above each positive density threshold, a radial mass-bounded family has a common finite support radius.
Use: a bounded compactly supported majorant for soft tests along the actual radial compactness subsequence.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the proved pointwise radial estimate m(x)≤M/(2|x|) falls below t outside the chosen radius. -/
theorem softTest_radial_support (m : L1Source) (hs : SymmetricDecreasing m.value)
    {M t δ : ℝ} (hM : m.mass ≤ M) (ht : 0 < t) (hδ : 0 ≤ δ) {x : ℝ}
    (hx : M/(2*t)+1 < |x|) : softTest t δ (m.value x)=0 := by
  -- A strictly larger radius avoids any boundary issue in the eventual indicator majorant.
  have hM0 : 0 ≤ M := (integral_nonneg m.nonneg).trans hM
  have hdiv : M/(2*t) < |x| := (lt_add_one _).trans hx
  have hx0 : 0 < |x| := (div_nonneg hM0 (by positivity)).trans_lt hdiv
  apply softTest_zero hδ
  apply (mass_tail m.integrable m.nonneg hs hM (abs_pos.mp hx0)).trans
  rw [div_le_iff₀ (by positivity : 0 < 2*|x|)]
  have hb := (div_lt_iff₀ (by positivity : 0 < 2*t)).mp hdiv
  nlinarith

/-- Pointwise radial compactness preserves every soft-test integral, without assuming global mass convergence.
Use: identifies the general radial limit's distribution by comparison with the original L1 approximants.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the positive test threshold gives one common compact spatial support,
the clipping height bounds the integrand, and dominated convergence uses the actual almost-everywhere limit. -/
theorem softTest_integral_limit_radial (m : ℕ → Density) (q : L1Source)
    (hs : ∀ n, SymmetricDecreasing (m n).value) {M : ℝ} (hM : ∀ n, (m n).mass ≤ M)
    (hl : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x)))
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) :
    Tendsto (fun n => ∫ x, softTest t δ ((m n).value x)) atTop
      (𝓝 (∫ x, softTest t δ (q.value x))) := by
  -- This domination does not use exact mass or root-mass preservation, avoiding a circular tightness argument.
  let R := M/(2*t)+1
  let B := (Icc (-R) R).indicator (fun _ : ℝ => δ)
  apply tendsto_integral_of_dominated_convergence B
  · exact fun n => ((softTest_lipschitz t δ).continuous.measurable.comp (m n).measurable).aestronglyMeasurable
  · exact (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  · intro n
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (softTest_bounds t hδ _).1]
    by_cases hx : x ∈ Icc (-R) R
    · simpa only [B,indicator_of_mem hx] using (softTest_bounds t hδ ((m n).value x)).2
    · have hr : R < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
      rw [softTest_radial_support (m n) (hs n) (hM n) ht hδ hr]
      simp only [B,indicator_of_notMem hx,le_refl]
  · exact hl.mono fun x hx => ((softTest_lipschitz t δ).continuous.tendsto (q.value x)).comp hx

end
end jacobi.Rearrangement
