import jacobi.Variational.Problem
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: jacobi, Appendix D.1 (lower semicontinuity).
Fatou semicontinuity is proved for the literal extended energy and root mass
under almost-everywhere convergence. No compactness or minimizer existence is
assumed in these analytic limit lemmas; those are separate proof obligations.
Source: the Lebesgue Fatou lemma in mathlib.
Use: applies once to the energy, mass and root-mass integrands in Compactness.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Fatou semicontinuity for every continuous nonnegative extended observation.
Use: applies once to the energy, mass and root-mass integrands in Compactness.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: continuity identifies the pointwise liminf with the proposed limit;
Fatou then gives the extended-integral inequality. -/
theorem continuous_integrand_liminf {f : ℕ → ℝ → ℝ} {q : ℝ → ℝ}
    (hf : ∀ n, Measurable (f n)) (hlim : ∀ᵐ x, Tendsto (fun n => f n x) atTop (𝓝 (q x)))
    (Φ : ℝ → ℝ≥0∞) (hΦ : Continuous Φ) :
    (∫⁻ x, Φ (q x)) ≤ liminf (fun n => ∫⁻ x, Φ (f n x)) atTop := by
  -- Almost-everywhere convergence is sufficient; no control of the value at the origin is needed.
  have he : (fun x => Φ (q x)) =ᵐ[volume]
      (fun x => liminf (fun n => Φ (f n x)) atTop) := by
    filter_upwards [hlim] with x hx
    exact ((hΦ.tendsto (q x)).comp hx).liminf_eq.symm
  rw [lintegral_congr_ae he]
  exact lintegral_liminf_le (fun n => hΦ.measurable.comp (hf n))

/-- The actual finite-energy cost equals its extended Lebesgue integral.
Use: ensures Fatou semicontinuity concerns exactly the variational objective.
Article: jacobi, Lemma D.1.
Proof: identify ofReal of a nonnegative integrable function's integral with its lintegral. -/
theorem Density.cost_eq_lintegral (m : Density) :
    m.cost = ∫⁻ x, ENNReal.ofReal (m.value x^(3/2 : ℝ)) :=
  ofReal_integral_eq_lintegral_ofReal m.energy_integrable
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (m.nonneg x) _)

/-- Energy is lower semicontinuous under almost-everywhere convergence of actual densities.
Use: the objective survives the minimizing-sequence compactness limit.
Article: jacobi, Lemma D.1.
Proof: the positive real-power integrand is continuous, so apply the common Fatou lemma. -/
theorem energy_liminf (m : ℕ → Density) (q : Density)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x))) :
    q.cost ≤ liminf (fun n => (m n).cost) atTop := by
  simp_rw [Density.cost_eq_lintegral]
  exact continuous_integrand_liminf (fun n => (m n).measurable) hlim
    (fun v => ENNReal.ofReal (v^(3/2 : ℝ)))
    (ENNReal.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num)))

/-- Root mass is lower semicontinuous, including the infinite-root-mass case.
Use: preserves the root-mass constraint in the stronger Transfer relaxation.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: square root and ofReal are continuous; apply Fatou to their composition. -/
theorem rootMass_liminf (m : ℕ → Density) (q : Density)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x))) :
    q.rootMass ≤ liminf (fun n => (m n).rootMass) atTop :=
  continuous_integrand_liminf (fun n => (m n).measurable) hlim
    (fun v => ENNReal.ofReal (Real.sqrt v))
    (ENNReal.continuous_ofReal.comp Real.continuous_sqrt)

/-- Mass is lower semicontinuous under almost-everywhere convergence.
Use: keeps the limiting mass within its upper bound even without tightness.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: apply Fatou to the nonnegative density itself and use its integrability. -/
theorem mass_liminf (m : ℕ → Density) (q : Density)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x))) :
    ENNReal.ofReal q.mass ≤ liminf (fun n => ENNReal.ofReal (m n).mass) atTop := by
  have he (p : Density) : ENNReal.ofReal p.mass = ∫⁻ x, ENNReal.ofReal (p.value x) :=
    ofReal_integral_eq_lintegral_ofReal p.integrable (Filter.Eventually.of_forall p.nonneg)
  simp_rw [he]
  exact continuous_integrand_liminf (fun n => (m n).measurable) hlim _ ENNReal.continuous_ofReal

/-- A uniformly bounded nonnegative integral remains finite at an almost-everywhere limit.
Use: constructs the limiting variational density instead of assuming its L1 membership.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Source: the Lebesgue Fatou lemma.
Proof: bound the extended limit integral by ofReal(C), deduce integrability,
then recover the ordinary real integral inequality. -/
theorem integrable_limit_of_bound {f : ℕ → ℝ → ℝ} {q : ℝ → ℝ} {C : ℝ}
    (hf : ∀ n, Integrable (f n)) (hfm : ∀ n, Measurable (f n))
    (hfn : ∀ n x, 0 ≤ f n x) (hqm : Measurable q) (hqn : ∀ x, 0 ≤ q x)
    (hlim : ∀ᵐ x, Tendsto (fun n => f n x) atTop (𝓝 (q x)))
    (hC : ∀ n, (∫ x, f n x) ≤ C) : Integrable q ∧ (∫ x, q x) ≤ C := by
  -- Work with extended integrals until integrability of the limit has been established.
  have hb : (∫⁻ x, ENNReal.ofReal (q x)) ≤ ENNReal.ofReal C := by
    apply (continuous_integrand_liminf hfm hlim ENNReal.ofReal ENNReal.continuous_ofReal).trans
    apply le_trans (liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)) (liminf_const _).le
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (Filter.Eventually.of_forall (hfn n))]
    exact ENNReal.ofReal_le_ofReal (hC n)
  have hi : Integrable q :=
    (lintegral_ofReal_ne_top_iff_integrable hqm.aestronglyMeasurable
      (Filter.Eventually.of_forall hqn)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  have hC0 : 0 ≤ C := (integral_nonneg (hfn 0)).trans (hC 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hqn)] at hb
  exact ⟨hi,(ENNReal.ofReal_le_ofReal_iff hC0).mp hb⟩

/-- Every measurable nonnegative a.e. limit with uniformly bounded mass and energy
belongs to the actual variational domain and retains both bounds.
Use: the construction step in Compactness and the direct minimizer-existence argument.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: apply the proved finite-integral Fatou lemma to q and q^(3/2), then
assemble the literal density with its derived, rather than postulated, integrability. -/
theorem finite_energy_limit (m : ℕ → Density) {q : ℝ → ℝ} (hqm : Measurable q)
    (hqn : ∀ x, 0 ≤ q x)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q x)))
    {M E : ℝ} (hM : ∀ n, (m n).mass ≤ M) (hE : ∀ n, (m n).energy ≤ E) :
    ∃ p : Density, p.value=q ∧ p.mass ≤ M ∧ p.energy ≤ E := by
  -- The two actual integral bounds supply both integrability fields of Density.
  have hm := integrable_limit_of_bound (fun n => (m n).integrable)
    (fun n => (m n).measurable) (fun n => (m n).nonneg) hqm hqn hlim hM
  have hc : Continuous (fun v : ℝ => v^(3/2 : ℝ)) := Real.continuous_rpow_const (by norm_num)
  have he := integrable_limit_of_bound (fun n => (m n).energy_integrable)
    (fun n => hc.measurable.comp (m n).measurable)
    (fun n x => Real.rpow_nonneg ((m n).nonneg x) _)
    (hc.measurable.comp hqm) (fun x => Real.rpow_nonneg (hqn x) _)
    (hlim.mono (fun x hx => (hc.tendsto (q x)).comp hx)) hE
  exact ⟨⟨⟨q,hqm,hqn,hm.1⟩,he.1⟩,rfl,hm.2,he.2⟩

end
end jacobi.Variational
