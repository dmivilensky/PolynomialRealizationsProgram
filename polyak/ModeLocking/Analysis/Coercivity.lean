import polyak.ModeLocking.Analysis.CompactCover

/-! A negative jet cover yields a global quadratic distance penalty. -/
noncomputable section
namespace polyak.ModeLocking.Analysis
open Set Metric

theorem NegativeJetCover.quadratic_coercivity {a b:ℝ} {Z:Finset ℝ} {f:ℝ→ℝ}
    (D:NegativeJetCover a b Z f) (hne:Z.Nonempty) :
    ∃c:ℝ,0<c ∧ ∀x∈Icc a b,c*(infDist x (Z:Set ℝ))^2≤-f x := by
  classical
  let c:=min (D.curvature/2) (D.margin/((b-a)^2+1))
  have hc:0<c:=lt_min (by positivity [D.curvature_pos]) (by positivity [D.margin_pos])
  refine ⟨c,hc,?_⟩
  intro x hx
  have hd:0≤ infDist x (Z:Set ℝ):=infDist_nonneg
  by_cases hnear:∃z∈Z,|x-z|<D.radius
  · obtain ⟨z,hz,hxz⟩:=hnear
    have ht:f x≤-D.curvature*(x-z)^2/2:=by
      apply quadratic_upper_bound D.smooth (D.centers z hz) hx (D.value_zero z hz) (D.slope_zero z hz)
      intro y hy
      apply D.local_bound z hz y (uIcc_subset_Icc (D.centers z hz) hx hy)
      exact (abs_sub_le_of_mem_segment hy).trans hxz.le
    have hdist:infDist x (Z:Set ℝ)≤|x-z|:=by simpa only [Real.dist_eq] using infDist_le_dist_of_mem (show z∈(Z:Set ℝ) from hz)
    have hsq:(infDist x (Z:Set ℝ))^2≤(x-z)^2:=by nlinarith [sq_abs (x-z)]
    have hm:c*(infDist x (Z:Set ℝ))^2≤(D.curvature/2)*(x-z)^2:=
      mul_le_mul (min_le_left _ _) hsq (sq_nonneg _) (by positivity [D.curvature_pos])
    nlinarith
  · push Not at hnear
    have ht:=D.away_bound x hx hnear
    obtain ⟨z,hz⟩:=hne
    have hzmem:=D.centers z hz
    have hdist:infDist x (Z:Set ℝ)≤|x-z|:=by simpa only [Real.dist_eq] using infDist_le_dist_of_mem (show z∈(Z:Set ℝ) from hz)
    have hB:|x-z|≤b-a:=abs_le.mpr ⟨by linarith [hzmem.2,hx.1],by linarith [hx.2,hzmem.1]⟩
    have hsq:(infDist x (Z:Set ℝ))^2≤(b-a)^2+1:=by
      have hb:0≤b-a:=by linarith [hx.1,hx.2]
      nlinarith
    have hm:c*(infDist x (Z:Set ℝ))^2≤(D.margin/((b-a)^2+1))*((b-a)^2+1):=
      mul_le_mul (min_le_right _ _) hsq (sq_nonneg _) (by positivity [D.margin_pos])
    rw [div_mul_cancel₀ _ (by positivity : (b-a)^2+1≠0)] at hm
    linarith

/-- Finite nondegenerate zeros imply coercivity; no distance estimate is a premise. -/
theorem finite_zero_quadratic_coercivity {a b:ℝ} {Z:Finset ℝ} {f:ℝ→ℝ}
    (hne:Z.Nonempty) (hz:∀z∈Z,z∈Icc a b)
    (hf:∀x∈Icc a b,ContDiffAt ℝ 2 f x)
    (hc2:ContinuousOn (iteratedDeriv 2 f) (Icc a b))
    (hzero:∀z∈Z,f z=0) (hslope:∀z∈Z,deriv f z=0)
    (hcurv:∀z∈Z,iteratedDeriv 2 f z<0)
    (hstrict:∀x∈Icc a b,x∉Z→f x<0) :
    ∃c:ℝ,0<c ∧ ∀x∈Icc a b,c*(infDist x (Z:Set ℝ))^2≤-f x := by
  obtain ⟨D⟩:=exists_negativeJetCover hne hz hf hc2 hzero hslope hcurv hstrict
  exact D.quadratic_coercivity hne

end polyak.ModeLocking.Analysis
