import krylov.XR.ConditionalFeasibility
import krylov.XR.KnownConditionalFibre
import krylov.XR.ConditionalColumns

/-!
Article: main_krylov, prop:cond(b), exact data-only optimization.
Use: compare the true known-base radius along every possible physical
base diagonal, then attain the printed data-only radius at the genuine
lower-root spectral completion. Source: two rational monotonicity
identities and the exact two-dimensional spectral endpoint matrix.
-/
namespace krylov.XR
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

/-- On the negative diagonal half-line the genuine conditional radius
decreases as the hidden base diagonal increases. Article: prop:cond(b). -/
theorem conditional_negative_monotone {ω t a b : ℝ} (hω : 0<ω) (ht : 0≤t)
    (hab : a≤b) (hb : b≤0) :
    ω-t*(1+b)/(ω-b)≤ω-t*(1+a)/(ω-a) := by
  have ha : a≤0 := hab.trans hb
  have hd₁ : 0<ω-a := by linarith
  have hd₂ : 0<ω-b := by linarith
  have hq : t*(1+a)/(ω-a)≤t*(1+b)/(ω-b) := by
    apply (div_le_div_iff₀ hd₁ hd₂).mpr
    nlinarith [mul_nonneg (mul_nonneg ht (by linarith : 0≤ω+1)) (sub_nonneg.mpr hab)]
  linarith

/-- On the positive diagonal half-line the radius increases with the
hidden diagonal when the original old budget is below one.
Article: main_krylov, prop:cond(b). -/
theorem conditional_positive_monotone {ω t a b : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (ht : 0≤t) (ha : 0≤a) (hab : a≤b) :
    ω-t*(1+a)/(ω+a)≤ω-t*(1+b)/(ω+b) := by
  have hb : 0≤b := ha.trans hab
  have hd₁ : 0<ω+a := by linarith
  have hd₂ : 0<ω+b := by linarith
  have hq : t*(1+b)/(ω+b)≤t*(1+a)/(ω+a) := by
    apply (div_le_div_iff₀ hd₂ hd₁).mpr
    nlinarith [mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hω₁.le)) (sub_nonneg.mpr hab)]
  linarith

/-- At either true boundary root the scalar completion collapses and
its exact worst hidden modulus is the modulus of that root.
Article: main_krylov, prop:cond(b). -/
theorem conditional_endpoint_radius {ω t k : ℝ} (hω : 0<ω)
    (hq : k^2+t*k+t=ω^2) : ω-t*(1+k)/(ω+|k|)=|k| := by
  have hd : ω+|k|≠0 := ne_of_gt (by positivity)
  have hs : |k|^2=k^2 := sq_abs k
  have he : t*(1+k)/(ω+|k|)=ω-|k| := by
    apply (div_eq_iff hd).mpr
    nlinarith only [hq,hs]
  rw [he]
  ring

/-- Every genuine explanation of the observed normalized defect obeys
the data-only conditional-radius upper bound. Article: prop:cond(b). -/
theorem unknown_conditional_upper {ω t δ k y : ℝ} (hω : 0<ω) (hω₁ : ω<1) (ht : 0≤t)
    (hobserved : δ^2=t*(1+k)) (hbudget : ‖conditionalMatrix y δ k‖≤ω) :
    |y|≤ -conditionalKlo ω t := by
  have hfeas := conditionalMatrix_column_feasible y δ k ω hω.le hbudget
  have hk : |k|≤ω := by nlinarith [sq_abs k,abs_nonneg k,sq_nonneg δ]
  have hkpos : 0<1+k := by linarith [(abs_le.mp hk).1]
  have hq : k^2+t*k+t≤ω^2 := by nlinarith only [hfeas,hobserved]
  have htfeas := conditional_feasibility_necessary hω hω₁ hkpos hq
  obtain ⟨hd,hkm,hkmn,horder,hloabs,hhiabs,hqlo,hqhi,hkhi⟩ :=
    conditional_endpoint_geometry hω hω₁ ht htfeas
  have hbetween := conditional_hidden_diagonal_between hd hq
  have hactual := (knownConditionalFibre hω hfeas).2 ⟨y,hbudget,rfl⟩
  rw [hobserved] at hactual
  by_cases hk₀ : 0≤k
  · have hp : 0≤conditionalKhi ω t := hk₀.trans hbetween.2
    have hm := conditional_positive_monotone hω hω₁ ht hk₀ hbetween.2
    rw [abs_of_nonneg hk₀] at hactual
    have he := conditional_endpoint_radius hω hqhi
    rw [abs_of_nonneg hp] at he
    exact (hactual.trans (hm.trans_eq he)).trans hkhi
  · have hk₀' : k≤0 := (lt_of_not_ge hk₀).le
    have hm := conditional_negative_monotone hω ht hbetween.1 hk₀'
    rw [abs_of_nonpos hk₀',←sub_eq_add_neg] at hactual
    have he := conditional_endpoint_radius hω hqlo
    rw [abs_of_nonpos hkmn,←sub_eq_add_neg] at he
    exact hactual.trans (hm.trans_eq he)

/-- An actual traceless two-dimensional spectral completion attains the
data-only bound and the exact observed normalized cross information.
Article: main_krylov, prop:cond(b), sharpness already in n=2. -/
theorem unknown_conditional_attainment {ω t : ℝ} (hω : 0<ω) (hω₁ : ω<1) (ht : 0≤t)
    (hfeasible : t≤2-2*Real.sqrt (1-ω^2)) :
    ∃ δ k y : ℝ,δ^2=t*(1+k) ∧ ‖conditionalMatrix y δ k‖≤ω ∧
      |y|= -conditionalKlo ω t := by
  obtain ⟨_hd,hkm,hkmn,_horder,_hloabs,_hhiabs,hqlo,_hqhi,_hkhi⟩ :=
    conditional_endpoint_geometry hω hω₁ ht hfeasible
  let k := conditionalKlo ω t
  let δ := Real.sqrt (t*(1+k))
  have hs : δ^2=t*(1+k) := Real.sq_sqrt (mul_nonneg ht hkm.le)
  refine ⟨δ,k,-k,hs,?_,?_⟩
  · rw [conditionalMatrix_traceless_norm]
    have he : δ^2+k^2=ω^2 := by dsimp only [k] at hs ⊢; nlinarith only [hqlo,hs]
    rw [he,Real.sqrt_sq hω.le]
  · exact abs_of_nonneg (neg_nonneg.mpr hkmn)

/-- The source's printed radical is exactly minus the genuine lower
completion root, including zero observed defect. Article: prop:cond(b). -/
theorem unknownConditionalRadius_root (ω δ fresh : ℝ) :
    unknownConditionalRadius ω δ fresh= -conditionalKlo ω (δ^2)+fresh := by
  have he : 4*ω^2-4*δ^2+δ^4=conditionalDiscriminant ω (δ^2) := by
    unfold conditionalDiscriminant
    ring
  unfold unknownConditionalRadius conditionalKlo
  rw [he]
  ring

/-- The printed data-only radius is the true attained maximum on all
spectral-budget explanations of the normalized observed data.
Article: main_krylov, prop:cond(b). -/
theorem unknownConditionalFibre {ω δobs : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (hfeasible : δobs^2≤2-2*Real.sqrt (1-ω^2)) :
    IsGreatest {r : ℝ | ∃ δ k y : ℝ,δ^2=δobs^2*(1+k) ∧
      ‖conditionalMatrix y δ k‖≤ω ∧ r=|y|}
      (unknownConditionalRadius ω δobs 0) := by
  rw [unknownConditionalRadius_root,add_zero]
  constructor
  · obtain ⟨δ,k,y,ho,hb,hy⟩ := unknown_conditional_attainment hω hω₁ (sq_nonneg δobs) hfeasible
    exact ⟨δ,k,y,ho,hb,hy.symm⟩
  · rintro r ⟨δ,k,y,ho,hb,rfl⟩
    exact unknown_conditional_upper hω hω₁ (sq_nonneg δobs) ho hb

end
end krylov.XR
