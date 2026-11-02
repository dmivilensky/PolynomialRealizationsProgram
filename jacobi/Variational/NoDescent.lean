import jacobi.Variational.DensityCone
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: jacobi, Lemma D.3.
Actual constrained minimality excludes an objective-decreasing, spectrally
increasing density direction. The proof constructs a real feasible convex
segment point: the objective decreases by its proved integral derivative,
the spectral constraint increases despite the quadratic remainder, and
the mass constraint is preserved in both the active and slack cases.
Source: the article's first-variation argument and one-sided derivative limits.
Use: converts the proved objective first variation into a feasible density with strictly lower energy.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A strictly negative classical derivative gives actual strict descent on a short right interval.
Use: converts the proved objective first variation into a feasible density with strictly lower energy.
Article: jacobi, Lemma D.3.
Proof: the right difference quotient tends to the negative derivative and has the same sign as the positive increment. -/
theorem HasDerivAt.eventually_right_descent {f : ℝ → ℝ} {c : ℝ}
    (hf : HasDerivAt f c 0) (hc : c<0) : ∀ᶠ t in 𝓝[>] (0:ℝ),f t<f 0 := by
  have h := hf.tendsto_slope_zero_right.eventually (Iio_mem_nhds hc)
  filter_upwards [h,self_mem_nhdsWithin] with t ht ht0
  change t⁻¹*(f (0+t)-f 0)<0 at ht
  rw [zero_add] at ht
  have htp : 0<t := ht0
  apply sub_neg.mp
  by_contra! h
  exact (not_lt_of_ge (mul_nonneg (inv_pos.mpr htp).le h)) ht

/-- Actual minimality and the proved quadratic spectral expansion exclude every strict feasible descent direction.
Use: discharges the separation theorem's disjointness hypothesis from the original variational problem.
Article: jacobi, Lemma D.3.
Proof: choose a sufficiently short positive density segment. Its objective
decreases by the genuine energy derivative; its spectral linear gain exceeds
the quadratic error. Continuity of the affine mass handles slack constraints,
while a strictly negative mass direction handles the active case. -/
theorem no_strict_density_descent (m q : Density) (Φ : Density → ℝ) (γ : ℝ → ℝ)
    {M T C r : ℝ} (hC : 0<C) (hr : 0<r) (hmM : m.mass≤M) (hmT : T≤Φ m)
    (hmin : ∀ v : Density,v.mass≤M → T≤Φ v → m.energy≤v.energy)
    (hvar : ∀ v : Density,(∫ x,|v.value x-m.value x|)≤r →
      |Φ v-Φ m-(∫ x,γ x*(v.value x-m.value x))|≤C*(∫ x,|v.value x-m.value x|)^2) :
    ¬((3/2:ℝ)*(∫ x,sqrt (m.value x)*(q.value x-m.value x))<0 ∧
      (m.mass=M → q.mass<m.mass) ∧ 0<∫ x,γ x*(q.value x-m.value x)) := by
  -- The strictly improving derivative coordinates must produce one actual admissible competitor.
  rintro ⟨hE,hMass,hG⟩
  let N := ∫ x,|q.value x-m.value x|
  let G := ∫ x,γ x*(q.value x-m.value x)
  have hN : 0≤N := integral_nonneg fun _ => abs_nonneg _
  let η := min 1 (min (r/(N+1)) (G/(C*N^2+1)))
  have hη : 0<η := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hη1 : η≤1 := min_le_left _ _
  have hηr : η≤r/(N+1) := (min_le_right _ _).trans (min_le_left _ _)
  have hηG : η≤G/(C*N^2+1) := (min_le_right _ _).trans (min_le_right _ _)
  let E (t : ℝ) := ∫ x,(m.value x+t*(q.value x-m.value x))^(3/2:ℝ)
  have hEevent : ∀ᶠ t in 𝓝[>] (0:ℝ),E t<E 0 :=
    HasDerivAt.eventually_right_descent (energy_hasDerivAt m q) hE
  have hMevent : ∀ᶠ t in 𝓝[>] (0:ℝ),m.mass+t*(q.mass-m.mass)≤M := by
    by_cases hactive : m.mass=M
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hqm := hMass hactive
      have htp : 0<t := ht
      rw [← hactive]
      nlinarith
    · have hslack : m.mass<M := lt_of_le_of_ne hmM hactive
      have hc : Continuous (fun t : ℝ => m.mass+t*(q.mass-m.mass)) := by fun_prop
      have h := hc.continuousAt.eventually (Iio_mem_nhds
        (show m.mass+(0:ℝ)*(q.mass-m.mass)<M by simpa using hslack))
      exact (h.filter_mono nhdsWithin_le_nhds).mono fun _ ht => ht.le
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ),t<η := by
    have h : ∀ᶠ t : ℝ in 𝓝 0,t<η := Iio_mem_nhds hη
    exact h.filter_mono nhdsWithin_le_nhds
  obtain ⟨t,htE,htM,htη,htpos⟩ := (hEevent.and (hMevent.and (hsmall.and self_mem_nhdsWithin))).exists
  have ht0 : 0<t := htpos
  have ht1 : t≤1 := htη.le.trans hη1
  let v := m.segment q t ht0.le ht1
  have hvM : v.mass≤M := by rw [Density.segment_mass]; exact htM
  have hvE : v.energy<m.energy := by
    have he : v.energy=E t := integral_congr_ae (Eventually.of_forall fun x => by
      change (m.segment q t ht0.le ht1).value x^(3/2:ℝ)=_
      rw [Density.segment_value])
    have he0 : E 0=m.energy := by simp only [E,zero_mul,add_zero,Density.energy]
    rwa [he,← he0]
  have hvN : (∫ x,|v.value x-m.value x|)=t*N := m.segment_l1 q t ht0.le ht1
  have hvsmall : (∫ x,|v.value x-m.value x|)≤r := by
    rw [hvN]
    have hh := (le_div_iff₀ (by positivity : 0<N+1)).mp hηr
    nlinarith
  have hvG : (∫ x,γ x*(v.value x-m.value x))=t*G := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change γ x*((m.segment q t ht0.le ht1).value x-m.value x)=t*(γ x*(q.value x-m.value x))
      rw [Density.segment_value]
      ring
  have hv := hvar v hvsmall
  rw [hvN,hvG] at hv
  have hbudget := (le_div_iff₀ (by positivity : 0<C*N^2+1)).mp hηG
  have hgain : C*(t*N)^2<t*G := by
    have he : 0<t*η := mul_pos ht0 hη
    have hh := mul_le_mul_of_nonneg_right hbudget ht0.le
    nlinarith [sq_nonneg N,mul_nonneg (by positivity : 0≤C*N^2) (sub_nonneg.mpr htη.le)]
  have hvT : T≤Φ v := hmT.trans (by
    have hh := (neg_le_abs (Φ v-Φ m-t*G)).trans hv
    linarith)
  exact (not_lt_of_ge (hmin v hvM hvT)) hvE

end
end jacobi.Variational
