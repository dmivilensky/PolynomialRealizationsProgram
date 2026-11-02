import jacobi.Variational.Translation

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Polarization sorts each pair reflected about a real point, placing its larger
value on the left half-line. This elementary operation preserves every Borel
function of the density, also for infinite nonnegative integrals. It is the
building block of the rearrangement argument, not yet its limiting theorem.
Source: polarization proof of rearrangement inequalities; Lieb and Loss, Analysis.
Use: pairs the two values sorted by polarization and preserves Lebesgue measure.
-/
namespace jacobi.Rearrangement
noncomputable section
open MeasureTheory Real Set
open jacobi.Variational
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Reflection about the point a.
Use: pairs the two values sorted by polarization and preserves Lebesgue measure.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def reflect (a x : ℝ) : ℝ := 2*a-x

/-- Reflecting twice returns the original point.
Use: pair identities and changes of variables in the polarization inequalities.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: expand the two affine reflections. -/
@[simp] theorem reflect_reflect (a x : ℝ) : reflect a (reflect a x)=x := by
  dsimp [reflect]
  ring

/-- The actual two-point polarization of a real-valued function.
Use: constructs each elementary rearrangement before passing to its radial limit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def polarize (a : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ a then max (m x) (m (reflect a x)) else min (m x) (m (reflect a x))

/-- A polarized value is one of the two original reflected values.
Use: integral domination without any monotonicity assumption on a composed Borel function.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: both maximum and minimum select one of their two arguments. -/
theorem polarize_eq_or (a : ℝ) (m : ℝ → ℝ) (x : ℝ) :
    polarize a m x=m x ∨ polarize a m x=m (reflect a x) := by
  rcases le_total (m x) (m (reflect a x)) with h | h <;>
    by_cases hx : x ≤ a <;> simp [polarize,hx,h]

/-- Every function of the two values has exactly the same pair sum after polarization.
Use: proves real and extended integral preservation by one reflection change of variables.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: away from the reflection point the two half-lines interchange; at the
reflection point the values coincide. Sorting merely permutes the two arguments. -/
theorem polarize_pair {E : Type*} [AddCommMonoid E] (F : ℝ → E)
    (a : ℝ) (m : ℝ → ℝ) (x : ℝ) :
    F (polarize a m x)+F (polarize a m (reflect a x))=F (m x)+F (m (reflect a x)) := by
  -- Treat the fixed reflection point first; otherwise the two sides receive max and min.
  by_cases he : x=a
  · subst x
    have hσ : reflect a a=a := by dsimp [reflect]; ring
    simp only [polarize,hσ,le_refl,ite_true,max_self]
  by_cases hx : x ≤ a
  · have hxa : x < a := lt_of_le_of_ne hx he
    have hy : ¬reflect a x ≤ a := by dsimp [reflect]; linarith
    simp only [polarize,ite_eq_left hx,ite_eq_right hy,reflect_reflect]
    rcases le_total (m x) (m (reflect a x)) with h | h
    · rw [max_eq_right h,min_eq_right h]
      exact add_comm _ _
    · rw [max_eq_left h,min_eq_left h]
  · have hy : reflect a x ≤ a := by dsimp [reflect]; linarith
    simp only [polarize,ite_eq_right hx,ite_eq_left hy,reflect_reflect]
    rcases le_total (m x) (m (reflect a x)) with h | h
    · rw [min_eq_left h,max_eq_left h]
    · rw [min_eq_right h,max_eq_right h]
      exact add_comm _ _

/-- Polarization preserves measurability of the literal density.
Use: all later density and spectral constructions use actual measurable functions.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: use measurable maxima and minima on the two measurable half-lines. -/
theorem polarize_measurable {m : ℝ → ℝ} (hm : Measurable m) (a : ℝ) :
    Measurable (polarize a m) :=
  Measurable.ite measurableSet_Iic
    (hm.max (hm.comp (measurable_const.sub measurable_id)))
    (hm.min (hm.comp (measurable_const.sub measurable_id)))

/-- On a preferred half-line the reflected pair is exactly the sorted pair.
Use: the pointwise Riesz polarization inequality, including its reflection boundary.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the reflected point is on the other half-line except at the fixed point,
where both values agree and maximum equals minimum. -/
theorem polarize_left_pair (a : ℝ) (m : ℝ → ℝ) {x : ℝ} (hx : x ≤ a) :
    polarize a m x=max (m x) (m (reflect a x)) ∧
      polarize a m (reflect a x)=min (m x) (m (reflect a x)) := by
  -- The fixed point must be handled explicitly because both closed half-lines contain it.
  refine ⟨ite_eq_left hx,?_⟩
  by_cases he : x=a
  · subst x
    have hσ : reflect a a=a := by dsimp [reflect]; ring
    simp [polarize,hσ]
  · have hxa : x < a := lt_of_le_of_ne hx he
    have hy : ¬reflect a x ≤ a := by dsimp [reflect]; linarith
    rw [polarize,ite_eq_right hy,reflect_reflect,min_comm]

/-- A Borel function of a polarized density remains integrable if it was integrable originally.
Use: licenses the real integral preservation theorem and finite-energy density constructor.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: each absolute value is dominated by the sum of the two reflected original absolute values. -/
theorem polarize_integrable_comp {m F : ℝ → ℝ} (hm : Measurable m) (hF : Measurable F)
    (hi : Integrable (fun x => F (m x))) (a : ℝ) :
    Integrable (fun x => F (polarize a m x)) := by
  -- This domination works for arbitrary signed Borel F, not only for increasing powers.
  apply (hi.abs.add (hi.comp_sub_left (2*a)).abs).mono'
    (hF.comp (polarize_measurable hm a)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    change |F (polarize a m x)| ≤ |F (m x)|+|F (m (reflect a x))|
    rcases polarize_eq_or a m x with h | h
    · rw [h]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [h]
      exact le_add_of_nonneg_left (abs_nonneg _)

/-- Polarization preserves every integrable Borel function of the density.
Use: exact mass and energy identities in the rearrangement construction.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: integrate the pair identity, change variables by reflection in the second
term on each side, and cancel the common factor two in the real numbers. -/
theorem integral_polarize_comp {m F : ℝ → ℝ} (hm : Measurable m) (hF : Measurable F)
    (hi : Integrable (fun x => F (m x))) (a : ℝ) :
    (∫ x, F (polarize a m x))=∫ x, F (m x) := by
  -- The reflection preserves the full integral, so no artificial half-line boundary term occurs.
  have hp := polarize_integrable_comp hm hF hi a
  have he := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (polarize_pair F a m))
  simp only [reflect] at he
  rw [integral_add hp (hp.comp_sub_left (2*a)),integral_add hi (hi.comp_sub_left (2*a))] at he
  rw [integral_sub_left_eq_self (fun x => F (polarize a m x)) volume (2*a),
    integral_sub_left_eq_self (fun x => F (m x)) volume (2*a)] at he
  linarith

/-- Polarization preserves every nonnegative Borel integral, including infinity.
Use: root-mass preservation without imposing finiteness, and preservation of superlevel measures.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: integrate the same pair identity with lintegral, use reflection invariance,
and cancel the finite nonzero factor two in ENNReal. -/
theorem lintegral_polarize_comp {m : ℝ → ℝ} {F : ℝ → ℝ≥0∞}
    (hm : Measurable m) (hF : Measurable F) (a : ℝ) :
    (∫⁻ x, F (polarize a m x))=∫⁻ x, F (m x) := by
  -- ENNReal cancellation here is by a finite multiplier, never by an infinite additive term.
  have hp := hF.comp (polarize_measurable hm a)
  have hq := hF.comp hm
  change Measurable (fun x => F (polarize a m x)) at hp
  change Measurable (fun x => F (m x)) at hq
  have he := lintegral_congr (μ := volume) (polarize_pair F a m)
  simp only [reflect] at he
  rw [lintegral_add_left hp,lintegral_add_left hq,
    lintegral_sub_left_eq_self (fun x => F (polarize a m x)) (2*a),
    lintegral_sub_left_eq_self (fun x => F (m x)) (2*a)] at he
  apply (ENNReal.mul_left_inj (c := 2) (by norm_num) (by simp)).mp
  simpa only [mul_two] using he

/-- Polarization preserves the measure of every strict superlevel set.
Use: identifies elementary polarizations as actual equimeasurable rearrangements,
not merely maps preserving a few selected moments of the density.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: apply extended Borel integral preservation to the indicator of (t,infinity). -/
theorem polarize_superlevel {m : ℝ → ℝ} (hm : Measurable m) (a t : ℝ) :
    volume {x | t < polarize a m x}=volume {x | t < m x} := by
  -- Indicator integration remains valid for infinite superlevel measures as well.
  let F : ℝ → ℝ≥0∞ := (Ioi t).indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator measurableSet_Ioi
  have he (q : ℝ → ℝ) (hq : Measurable q) :
      (∫⁻ x, F (q x))=volume {x | t < q x} := by
    have hs : MeasurableSet {x | t < q x} := hq measurableSet_Ioi
    rw [← lintegral_indicator_one hs]
    apply lintegral_congr
    intro x
    by_cases hx : t < q x <;> simp [F,hx]
  have h := lintegral_polarize_comp hm hF a
  rw [he _ (polarize_measurable hm a),he _ hm] at h
  exact h

/-- Polarization stays in the actual finite-energy variational domain.
Use: elementary admissible rearrangements in existence and Transfer proofs.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def _root_.jacobi.Variational.Density.polarize (m : Density) (a : ℝ) : Density where
  value := jacobi.Rearrangement.polarize a m.value
  measurable := polarize_measurable m.measurable a
  nonneg x := by
    rcases polarize_eq_or a m.value x with h | h <;> rw [h] <;> exact m.nonneg _
  integrable := polarize_integrable_comp m.measurable measurable_id m.integrable a
  energy_integrable := polarize_integrable_comp m.measurable
    (by fun_prop : Measurable (fun x : ℝ => x^(3/2 : ℝ))) m.energy_integrable a

/-- The actual polarized density has exactly the original mass and energy.
Use: replaces a minimizing density without changing its objective or mass constraint.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: specialize integral preservation to the identity and the 3/2-power function. -/
theorem _root_.jacobi.Variational.Density.polarize_integrals (m : Density) (a : ℝ) :
    (m.polarize a).mass=m.mass ∧ (m.polarize a).energy=m.energy :=
  ⟨integral_polarize_comp m.measurable measurable_id m.integrable a,
    integral_polarize_comp m.measurable (by fun_prop : Measurable (fun x : ℝ => x^(3/2 : ℝ)))
      m.energy_integrable a⟩

/-- The root mass is exactly preserved even when it is infinite.
Use: elementary rearrangements preserve the stronger root-mass relaxation's admissibility.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: apply the proved extended integral invariance to ofReal(sqrt(x)). -/
theorem _root_.jacobi.Variational.Density.polarize_rootMass (m : Density) (a : ℝ) :
    (m.polarize a).rootMass=m.rootMass :=
  lintegral_polarize_comp m.measurable (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (sqrt x))) a

end
end jacobi.Rearrangement
