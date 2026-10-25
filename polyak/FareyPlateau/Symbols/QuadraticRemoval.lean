import polyak.FareyPlateau.Symbols.PhaseFloor
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! A canonical removable quadratic quotient.  Two divided slopes give
the exact quotient off the contact and an analytic value at the contact. -/
noncomputable section
namespace polyak.FareyPlateau.Symbols
open Set

theorem analyticAt_dslope_same {f : ℝ→ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) :
    AnalyticAt ℝ (dslope f a) a := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

def quadraticQuotient (f : ℝ→ℝ) (a : ℝ) : ℝ→ℝ := dslope (dslope f a) a

theorem quadraticQuotient_analytic {f : ℝ→ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) :
    AnalyticAt ℝ (quadraticQuotient f a) a :=
  analyticAt_dslope_same (analyticAt_dslope_same hf)

theorem quadraticQuotient_factor {f : ℝ→ℝ} {a : ℝ}
    (h0 : f a=0) (h1 : deriv f a=0) (x : ℝ) :
    (x-a)^2*quadraticQuotient f a x=f x := by
  have hfirst := sub_smul_dslope f a x
  have hsecond := sub_smul_dslope (dslope f a) a x
  simp only [smul_eq_mul,dslope_same,h0,h1,sub_zero] at hfirst hsecond
  unfold quadraticQuotient
  linear_combination hfirst+(x-a)*hsecond

theorem quadraticQuotient_eq {f : ℝ→ℝ} {a x : ℝ}
    (h0 : f a=0) (h1 : deriv f a=0) (hx : x≠a) :
    quadraticQuotient f a x=f x/(x-a)^2 := by
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hx))).mpr
  simpa only [mul_comm] using quadraticQuotient_factor h0 h1 x

theorem quadraticQuotient_continuousOn {f : ℝ→ℝ} {a : ℝ} {S : Set ℝ}
    (hf : ContinuousOn f S) (ha : AnalyticAt ℝ f a) :
    ContinuousOn (quadraticQuotient f a) S := by
  intro x hx
  by_cases he : x=a
  · subst x
    exact (quadraticQuotient_analytic ha).continuousAt.continuousWithinAt
  · apply (continuousWithinAt_dslope_of_ne he).mpr
    exact (continuousWithinAt_dslope_of_ne he).mpr (hf x hx)

theorem quadraticQuotient_value {f : ℝ→ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a)
    (h0 : f a=0) (h1 : deriv f a=0) :
    quadraticQuotient f a a=(deriv (deriv f) a)/2 := by
  have hR := quadraticQuotient_analytic hf
  have hfun : f=(fun x=>(x-a)^2*quadraticQuotient f a x) :=
    funext (fun x=>(quadraticQuotient_factor h0 h1 x).symm)
  have hpow (j : ℕ) : iteratedDeriv j (fun x : ℝ=>(x-a)^2) a =
      if j=2 then 2 else 0 := by
    have he := congrFun (iteratedDeriv_comp_sub_const j (fun z : ℝ=>z^2) a) a
    rw [he,sub_self]
    rw [iteratedDeriv_fun_pow_zero]
    split_ifs <;> norm_num
  have he := iteratedDeriv_fun_mul (n:=2) (x:=a)
    (by fun_prop : ContDiffAt ℝ 2 (fun x : ℝ=>(x-a)^2) a)
    (hR.contDiffAt (n:=2))
  norm_num [Finset.sum_range_succ,hpow,iteratedDeriv_zero] at he
  rw [←hfun] at he
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at he
  linarith

end polyak.FareyPlateau.Symbols
