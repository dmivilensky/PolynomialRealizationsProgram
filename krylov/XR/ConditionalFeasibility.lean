import krylov.XR.ConditionalRadiusAlgebra

/-!
Article: main_krylov, prop:cond(b), data-only feasibility and endpoints.
Use: compute the actual hidden-diagonal interval from the normalized
observed defect, with every radical and positive base denominator justified.
Source: completing the real scalar quadratic and the arithmetic--geometric
mean square, without an assumed realizability interval.
-/
namespace krylov.XR
noncomputable section

/-- Discriminant of the original data-only hidden-diagonal constraint.
Article: main_krylov, prop:cond(b). -/
def conditionalDiscriminant (ω t : ℝ) : ℝ := t^2-4*t+4*ω^2

/-- The exact lower hidden-diagonal endpoint. Article: prop:cond(b). -/
def conditionalKlo (ω t : ℝ) : ℝ := (-t-Real.sqrt (conditionalDiscriminant ω t))/2

/-- The exact upper hidden-diagonal endpoint. Article: prop:cond(b). -/
def conditionalKhi (ω t : ℝ) : ℝ := (-t+Real.sqrt (conditionalDiscriminant ω t))/2

/-- Any genuine explanation of the observed normalized defect obeys
the exact printed data-only feasibility threshold. Article: prop:cond(b). -/
theorem conditional_feasibility_necessary {ω t k : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (hk : 0<1+k) (hq : k^2+t*k+t≤ω^2) : t≤2-2*Real.sqrt (1-ω^2) := by
  have hc : 0<1-ω^2 := by nlinarith
  have hs := Real.sq_sqrt hc.le
  have ha := sq_nonneg ((1+k)-Real.sqrt (1-ω^2))
  by_contra! ht
  have hp := mul_pos (sub_pos.mpr ht) hk
  nlinarith

/-- Feasible observed data give a nonnegative true discriminant and
strictly positive physical base denominators at both root endpoints.
Article: main_krylov, prop:cond(b). -/
theorem conditional_endpoint_geometry {ω t : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (ht : 0≤t) (hfeasible : t≤2-2*Real.sqrt (1-ω^2)) :
    0≤conditionalDiscriminant ω t ∧
    0<1+conditionalKlo ω t ∧
    conditionalKlo ω t≤0 ∧
    conditionalKlo ω t≤conditionalKhi ω t ∧
    |conditionalKlo ω t|≤ω ∧ |conditionalKhi ω t|≤ω ∧
    conditionalKlo ω t^2+t*conditionalKlo ω t+t=ω^2 ∧
    conditionalKhi ω t^2+t*conditionalKhi ω t+t=ω^2 ∧
    conditionalKhi ω t≤ -conditionalKlo ω t := by
  have hc : 0<1-ω^2 := by nlinarith
  have hs := Real.sq_sqrt hc.le
  have hspos := Real.sqrt_pos.mpr hc
  have ht₂ : t<2 := by linarith
  have hd : 0≤conditionalDiscriminant ω t := by
    unfold conditionalDiscriminant
    nlinarith [sq_nonneg (2-t-2*Real.sqrt (1-ω^2))]
  have hds := Real.sq_sqrt hd
  change Real.sqrt (conditionalDiscriminant ω t)^2=t^2-4*t+4*ω^2 at hds
  have hdn := Real.sqrt_nonneg (conditionalDiscriminant ω t)
  have hdu : Real.sqrt (conditionalDiscriminant ω t)<2-t := by
    nlinarith
  have hkl : 0<1+conditionalKlo ω t := by unfold conditionalKlo; linarith
  have horder : conditionalKlo ω t≤conditionalKhi ω t := by
    unfold conditionalKlo conditionalKhi
    linarith
  have hlo : conditionalKlo ω t≤0 := by unfold conditionalKlo; linarith
  have hqlo : conditionalKlo ω t^2+t*conditionalKlo ω t+t=ω^2 := by
    unfold conditionalKlo
    nlinarith only [hds]
  have hqhi : conditionalKhi ω t^2+t*conditionalKhi ω t+t=ω^2 := by
    unfold conditionalKhi
    nlinarith only [hds]
  have habslo : |conditionalKlo ω t|≤ω := by
    have hpos := mul_nonneg ht hkl.le
    nlinarith [sq_abs (conditionalKlo ω t),abs_nonneg (conditionalKlo ω t)]
  have habshi : |conditionalKhi ω t|≤ω := by
    have hpos := mul_nonneg ht (by linarith : 0≤1+conditionalKhi ω t)
    nlinarith [sq_abs (conditionalKhi ω t),abs_nonneg (conditionalKhi ω t)]
  refine ⟨hd,hkl,hlo,horder,habslo,habshi,hqlo,hqhi,?_⟩
  unfold conditionalKhi conditionalKlo
  linarith

/-- The original scalar constraint puts every possible hidden diagonal
between its two genuine root endpoints. Article: prop:cond(b). -/
theorem conditional_hidden_diagonal_between {ω t k : ℝ}
    (hdisc : 0≤conditionalDiscriminant ω t) (hq : k^2+t*k+t≤ω^2) :
    conditionalKlo ω t≤k ∧ k≤conditionalKhi ω t := by
  have hs := Real.sq_sqrt hdisc
  have hn := Real.sqrt_nonneg (conditionalDiscriminant ω t)
  have hsq : (2*k+t)^2≤conditionalDiscriminant ω t := by
    unfold conditionalDiscriminant
    nlinarith
  have hh : |2*k+t|≤Real.sqrt (conditionalDiscriminant ω t) := by
    nlinarith [sq_abs (2*k+t),abs_nonneg (2*k+t)]
  have ha := abs_le.mp hh
  unfold conditionalKlo conditionalKhi
  constructor <;> linarith

/-- Data-only consistency is exactly the article's threshold, with an
actual real hidden diagonal as witness in the physical interval.
Article: main_krylov, prop:cond(b). -/
theorem conditional_feasibility_iff {ω t : ℝ} (hω : 0<ω) (hω₁ : ω<1) (ht : 0≤t) :
    (∃ k : ℝ,|k|≤ω ∧ k^2+t*k+t≤ω^2) ↔ t≤2-2*Real.sqrt (1-ω^2) := by
  constructor
  · rintro ⟨k,hk,hq⟩
    have hk' : 0<1+k := by linarith [(abs_le.mp hk).1]
    exact conditional_feasibility_necessary hω hω₁ hk' hq
  · intro hf
    have he := conditional_endpoint_geometry hω hω₁ ht hf
    exact ⟨conditionalKlo ω t,he.2.2.2.2.1,he.2.2.2.2.2.2.1.le⟩

end
end krylov.XR
