import jacobi.RootMass.Calibration
import jacobi.Variational.ExtendedEnergy

/-!
Article: jacobi, Appendix D.5 (unrestricted inner problem).
The actual nonnegative objective is integrated in the extended reals over
all nonnegative L1 sources. Coercivity proves that every finite-cost source
has finite energy and finite root mass, so it genuinely belongs to the
finite domain used by the direct method. Infinite-cost competitors cannot
lower the infimum. No domain restriction changes the printed inner problem.
Source: nonnegative Lebesgue integration and the proved polynomial coercivity.
Use: includes sources with infinite energy or infinite root mass in the stated inner problem.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The literal extended root-mass inner objective of an arbitrary nonnegative L1 source.
Use: includes sources with infinite energy or infinite root mass in the stated inner problem.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def extendedCost (m : L1Source) (a b : ℝ) : ℝ≥0∞ := ∫⁻ x,ENNReal.ofReal (f a b (sqrt (m.value x)))

/-- The genuine full-domain inner infimum of the supplement.
Use: the exact finite-domain value and attainer also solve this literal unrestricted problem.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
-/
def extendedInner (a b T : ℝ) : ℝ≥0∞ := sInf ((fun m : L1Source => extendedCost m a b) '' {m | T≤observe m .second})

/-- Every finite full-domain objective constructs an actual finite-energy, finite-root density with the same literal source.
Use: removes all extra integrability hypotheses from the inner direct method and exact calibration.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: the actual nonnegative polynomial is integrable at finite extended
cost. Its proved positive coercivity dominates both the energy and root
integrands by integrable scalar multiples. These bounds construct the actual finite-domain density. -/
def finiteCostDensity {a b : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (m : L1Source)
    (hcost : extendedCost m a b≠∞) : RootDensity := by
  -- Both integrability fields are derived from the original extended objective.
  have hsqrt : Measurable (fun x => sqrt (m.value x)) := continuous_sqrt.measurable.comp m.measurable
  have hmeas : Measurable (fun x => f a b (sqrt (m.value x))) := by
    unfold f
    exact ((hsqrt.pow_const 3).add (measurable_const.mul (hsqrt.pow_const 2))).add (measurable_const.mul hsqrt)
  have hi : Integrable (fun x => f a b (sqrt (m.value x))) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Eventually.of_forall fun _ => f_nonneg ha hb.le (sqrt_nonneg _))).mp hcost
  have hc := coercivity_pos ha
  have hbound (x : ℝ) := f_coercive a hb.le (sqrt_nonneg (m.value x))
  have he : Integrable (fun x => m.value x^(3/2:ℝ)) := by
    apply (hi.div_const (coercivity a)).mono' ((m.measurable.pow_const (3/2:ℝ)).aestronglyMeasurable)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg (m.nonneg x) _),rpow_div_two_eq_sqrt 3 (m.nonneg x),rpow_ofNat]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hbound x,mul_nonneg (sq_nonneg b) (sqrt_nonneg (m.value x))]
  have hr : Integrable (fun x => sqrt (m.value x)) := by
    have hmr : AEStronglyMeasurable (fun x => sqrt (m.value x)) volume :=
      (continuous_sqrt.measurable.comp m.measurable).aestronglyMeasurable
    apply (hi.div_const (coercivity a*b^2)).mono' hmr
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)]
    apply (le_div_iff₀ (mul_pos hc (pow_pos hb 2))).mpr
    nlinarith [hbound x,pow_nonneg (sqrt_nonneg (m.value x)) 3]
  exact ⟨⟨m,he⟩,hr⟩

/-- The direct method's finite-domain infimum equals the literal full L1 inner problem.
Use: the printed exact value, attainment and activity carry no unproved energy or root-integrability premise.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: every finite-domain competitor is an unrestricted source with the
same actual objective. Conversely, a finite unrestricted cost constructs
a genuine finite-domain competitor by coercivity; an infinite cost is automatic. -/
theorem extendedInner_eq {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) : extendedInner a b T=inner a b T := by
  -- Both order comparisons use the actual defining sets, including infinite-cost sources.
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨m,hm,rfl⟩
    have hh : extendedInner a b T≤extendedCost m.toL1Source a b := sInf_le ⟨m.toL1Source,hm,rfl⟩
    exact hh.trans_eq (m.cost_eq_lintegral ha hb.le).symm
  · apply le_sInf
    rintro _ ⟨m,hm,rfl⟩
    change inner a b T≤extendedCost m a b
    by_cases hi : extendedCost m a b=∞
    · rw [hi]
      exact le_top
    · let q := finiteCostDensity ha hb m hi
      have hq : inner a b T≤q.cost a b := sInf_le ⟨q,hm,rfl⟩
      exact hq.trans_eq (q.cost_eq_lintegral ha hb.le)

/-- The full-domain inner problem has a genuine finite attained minimum and an active actual spectral constraint.
Use: the supplement's existence and activity conclusions concern the original full L1 problem.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: the already constructed actual compact optimizer has finite extended
cost, attains the unrestricted infimum by the proved domain identity, and
saturates its true moment by the proved amplitude variation. -/
theorem extendedInner_attained {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T) :
    ∃ m : RootDensity,SymmetricDecreasing m.value ∧ observe m.toDensity .second=T ∧
      extendedCost m.toL1Source a b=extendedInner a b T ∧ extendedInner a b T≠∞ := by
  -- The witness is the original attained minimizer used in the exact calibration.
  obtain ⟨P⟩ := profile_exists ha hb hT
  have he : extendedCost P.density.toL1Source a b=extendedInner a b T := by
    rw [extendedInner_eq ha hb,← P.optimal]
    exact (P.density.cost_eq_lintegral ha hb.le).symm
  exact ⟨P.density,P.radial,P.active,he,by rw [← he]; change (∫⁻ x,ENNReal.ofReal (f a b (sqrt (P.density.value x))))≠∞; rw [← P.density.cost_eq_lintegral ha hb.le]; exact ENNReal.ofReal_ne_top⟩

/-- Every unrestricted inner minimizer saturates its actual second-moment constraint.
Use: the activity conclusion has the complete L1 domain stated in the supplement.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: the actual attained inner value is finite. Coercivity therefore
constructs a genuine finite-energy, finite-root density from the minimizer.
The proved original amplitude-variation activity theorem then applies. -/
theorem extendedInner_active {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T)
    (m : L1Source) (hG : T≤observe m .second) (hmin : extendedCost m a b=extendedInner a b T) :
    observe m .second=T := by
  -- No integrability premise is imposed on the unrestricted minimizer.
  obtain ⟨_w,_hrad,_hactive,_hcost,hfinite⟩ := extendedInner_attained ha hb hT
  have hi : extendedCost m a b≠∞ := by rw [hmin]; exact hfinite
  let q := finiteCostDensity ha hb m hi
  have he : q.cost a b=inner a b T := by
    rw [q.cost_eq_lintegral ha hb.le]
    exact hmin.trans (extendedInner_eq ha hb)
  exact inner_constraint_active ha hb hT q hG he

/-- The literal full-L1 inner infimum has the exact value at its uniquely constructed actual parameter.
Use: closes the source's inner variational calculation on its unrestricted stated domain.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: combine the proved exact domain identity with the actual attained
quadrature formula at the constructed positive root. -/
theorem extendedInner_exact {a b T : ℝ} (ha : -(17/5:ℝ)≤a) (hb : 0<b) (hT : 0<T) :
    extendedInner a b T=ENNReal.ofReal (
      b^3*hat 3 a (sharp_parameter ha) (parameter a b T ha hb hT)+
      (a*b/2)*(b^2*hat 2 a (sharp_parameter ha) (parameter a b T ha hb hT))+
      b^3*hat 1 a (sharp_parameter ha) (parameter a b T ha hb hT)) := by
  rw [extendedInner_eq (sharp_parameter ha) hb]
  exact inner_exact ha hb hT (parameter_spec ha hb hT).1 (parameter_spec ha hb hT).2

/-- The root-mass calibration applies to every original nonnegative L1 source, including infinite-energy competitors.
Use: the final analytic bound has no extra finite-energy hypothesis.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: infinite extended energy is automatic. A finite-energy source
constructs an actual Density with the same mass, root integral and spectrum;
its literal admissibility and the proved calibration give the lower bound. -/
theorem root_calibration_L1 {a b M : ℝ} (ha : -(17/5:ℝ)≤a) (hb : 0<b)
    (T : Observation → ℝ) (hT : 0<T .second) (m : L1Source)
    (hm : m.mass=M) (hr : (∫⁻ x,ENNReal.ofReal (sqrt (m.value x)))≤1)
    (hG : T .second≤observe m .second) :
    ENNReal.ofReal (ellH a b M ha (parameter a b (T .second) ha hb hT))≤m.energyCost := by
  -- Finite energy is derived only when it is needed to represent a potentially improving competitor.
  by_cases hi : m.energyCost=∞
  · rw [hi]
    exact le_top
  · let q := m.finiteEnergyDensity hi
    have hq : rootInfimum {Observation.second} M T≤q.cost := sInf_le
      ⟨q,⟨hm,hr,fun i hi => by
        have he : i=Observation.second := by simpa only [mem_singleton_iff] using hi
        subst i
        exact hG⟩,rfl⟩
    exact (root_calibration ha hb T hT).trans (hq.trans_eq q.energyCost_eq_cost.symm)

end
end jacobi.RootMass
