import polyak.ModeLocking.Analysis.JetBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! A finite collection of strict quadratic maxima and a strict compact
complement give a global sign. The hypotheses are local derivative bounds,
not the sign conclusion. -/
noncomputable section
namespace polyak.ModeLocking.Analysis
open Set

theorem abs_sub_le_of_mem_segment {z x y:ℝ} (hy:y∈uIcc z x) : |y-z|≤|x-z| := by
  rcases le_total z x with h|h
  · rw [uIcc_of_le h] at hy
    rw [abs_of_nonneg (sub_nonneg.mpr hy.1),abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hy.2]
  · rw [uIcc_of_ge h] at hy
    rw [abs_of_nonpos (sub_nonpos.mpr hy.2),abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [hy.1]

structure NegativeJetCover (a b:ℝ) (Z:Finset ℝ) (f:ℝ→ℝ) where
  smooth : ∀x∈Icc a b,ContDiffAt ℝ 2 f x
  centers : ∀z∈Z,z∈Icc a b
  value_zero : ∀z∈Z,f z=0
  slope_zero : ∀z∈Z,deriv f z=0
  radius : ℝ
  radius_pos : 0<radius
  curvature : ℝ
  curvature_pos : 0<curvature
  margin : ℝ
  margin_pos : 0<margin
  local_bound : ∀z∈Z,∀x∈Icc a b,|x-z|≤radius→iteratedDeriv 2 f x≤-curvature
  away_bound : ∀x∈Icc a b,(∀z∈Z,radius≤|x-z|)→f x≤-margin

theorem NegativeJetCover.strict {a b:ℝ} {Z:Finset ℝ} {f:ℝ→ℝ}
    (D:NegativeJetCover a b Z f) {x:ℝ} (hx:x∈Icc a b) (hn:x∉Z) : f x<0 := by
  classical
  by_cases hnear:∃z∈Z,|x-z|<D.radius
  · obtain ⟨z,hz,hxz⟩:=hnear
    have hbound:f x≤-D.curvature*(x-z)^2/2:=by
      apply quadratic_upper_bound D.smooth (D.centers z hz) hx (D.value_zero z hz) (D.slope_zero z hz)
      intro y hy
      apply D.local_bound z hz y (uIcc_subset_Icc (D.centers z hz) hx hy)
      exact (abs_sub_le_of_mem_segment hy).trans hxz.le
    have hne:x-z≠0:=sub_ne_zero.mpr (fun he=>hn (he ▸ hz))
    have hp:0<D.curvature*(x-z)^2:=mul_pos D.curvature_pos (sq_pos_of_ne_zero hne)
    nlinarith
  · have hfar:∀z∈Z,D.radius≤|x-z|:=by
      push Not at hnear
      exact hnear
    exact (D.away_bound x hx hfar).trans_lt (neg_neg_of_pos D.margin_pos)

theorem NegativeJetCover.nonpos {a b:ℝ} {Z:Finset ℝ} {f:ℝ→ℝ}
    (D:NegativeJetCover a b Z f) {x:ℝ} (hx:x∈Icc a b) : f x≤0 := by
  classical
  by_cases hn:x∈Z
  · exact le_of_eq (D.value_zero x hn)
  · exact (D.strict hx hn).le

theorem NegativeJetCover.zero_iff {a b:ℝ} {Z:Finset ℝ} {f:ℝ→ℝ}
    (D:NegativeJetCover a b Z f) {x:ℝ} (hx:x∈Icc a b) : f x=0 ↔ x∈Z := by
  classical
  exact ⟨fun hz=>by by_contra hn;exact (D.strict hx hn).ne hz,fun hz=>D.value_zero x hz⟩

theorem NegativeJetCover.perturb {a b:ℝ} {Z:Finset ℝ} {f E:ℝ→ℝ}
    (D:NegativeJetCover a b Z f) (hE:∀x∈Icc a b,ContDiffAt ℝ 2 E x)
    (hEz:∀z∈Z,E z=0) (hEdz:∀z∈Z,deriv E z=0)
    {M0 M2:ℝ} (hM0:0≤M0) (hM2:0≤M2)
    (hB0:∀x∈Icc a b,|E x|≤M0) (hB2:∀x∈Icc a b,|iteratedDeriv 2 E x|≤M2) :
    ∃r:ℝ,0<r ∧ ∀ε:ℝ,|ε|<r→Nonempty (NegativeJetCover a b Z (fun x=>f x+ε*E x)) := by
  let r:=min (D.curvature/(2*(M2+1))) (D.margin/(2*(M0+1)))
  have hr:0<r:=lt_min (by positivity [D.curvature_pos]) (by positivity [D.margin_pos])
  refine ⟨r,hr,?_⟩
  intro ε hε
  have he2:|ε| *M2<D.curvature/2:=by
    have hε':|ε|<D.curvature/(2*(M2+1)):=hε.trans_le (min_le_left _ _)
    have hh:|ε| *(2*(M2+1))<D.curvature:=(lt_div_iff₀ (by positivity)).mp hε'
    nlinarith [abs_nonneg ε]
  have he0:|ε| *M0<D.margin/2:=by
    have hε':|ε|<D.margin/(2*(M0+1)):=hε.trans_le (min_le_right _ _)
    have hh:|ε| *(2*(M0+1))<D.margin:=(lt_div_iff₀ (by positivity)).mp hε'
    nlinarith [abs_nonneg ε]
  have hprod (x:ℝ) (hx:x∈Icc a b) : ε*E x≤|ε| *M0:=by
    exact (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hB0 x hx) (abs_nonneg ε))
  have hderiv (x:ℝ) (hx:x∈Icc a b) :
      iteratedDeriv 2 (fun y=>f y+ε*E y) x=iteratedDeriv 2 f x+ε*iteratedDeriv 2 E x:=by
    rw [iteratedDeriv_fun_add (D.smooth x hx) (contDiffAt_const.mul (hE x hx)),iteratedDeriv_const_mul_field]
  refine ⟨{
    smooth:=fun x hx=>(D.smooth x hx).add (contDiffAt_const.mul (hE x hx))
    centers:=D.centers
    value_zero:=by intro z hz;rw [D.value_zero z hz,hEz z hz,mul_zero,add_zero]
    slope_zero:=by
      intro z hz
      rw [deriv_fun_add ((D.smooth z (D.centers z hz)).differentiableAt (by norm_num))
        ((contDiffAt_const.mul (hE z (D.centers z hz))).differentiableAt (by norm_num)),
        deriv_const_mul_field,D.slope_zero z hz,hEdz z hz,mul_zero,add_zero]
    radius:=D.radius
    radius_pos:=D.radius_pos
    curvature:=D.curvature/2
    curvature_pos:=by positivity [D.curvature_pos]
    margin:=D.margin/2
    margin_pos:=by positivity [D.margin_pos]
    local_bound:=by
      intro z hz x hx hnear
      rw [hderiv x hx]
      have hb:ε*iteratedDeriv 2 E x≤|ε| *M2:=
        (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hB2 x hx) (abs_nonneg ε))
      have hh:=D.local_bound z hz x hx hnear
      linarith
    away_bound:=by intro x hx hfar;have hh:=D.away_bound x hx hfar;have hp:=hprod x hx;linarith}⟩

end polyak.ModeLocking.Analysis
