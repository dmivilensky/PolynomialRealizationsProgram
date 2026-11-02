import jacobi.Fredholm.CandidateProfiles

/-!
Article: jacobi, Appendix D.4.
The actual Green diagonal is the inverse of the printed phase integral.
Its inverse-coordinate definition is proved from an original spatial
quadrature with a level-set indicator, including convergence at the turn.
Source: genuine one-dimensional change of variables and strict radial monotonicity.
Use: identifies constructed arbitrary candidates with the source's inverse-coordinate definition.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- The actual optimizing Green branch is the inverse of the printed phase integral at every positive radius.
Use: identifies constructed arbitrary candidates with the source's inverse-coordinate definition.
Article: jacobi, Appendix D.4.
Proof: the observable indicating levels above g(x) is exactly the
indicator of the spatial interval (-x,x). Its true Green quadrature
therefore has value 2*x. Remove the level indicator by restricting to
(g(x),g0), then divide by two. Its positive integral also certifies
actual convergence of the phase integral at the turning endpoint. -/
theorem Optimizer.inverse_phase {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    {x : ℝ} (hx : 0<x) :
    IntervalIntegrable (fun v => 1/sqrt (phase P.A P.edge v)) volume (P.g hs.le x) (P.g hs.le 0) ∧
      x=∫ v in P.g hs.le x..P.g hs.le 0,1/sqrt (phase P.A P.edge v) := by
  -- A genuine spatial interval, rather than a formal antiderivative, supplies the inverse integral.
  let g := P.g hs.le
  let F := fun v : ℝ => if g x<v then (1:ℝ) else 0
  have habs (y : ℝ) : g |y|=g y := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_nonpos hy]
      exact (P.shape hs).2.2.1 y
  have hlevel (y : ℝ) : g x<g y ↔ y∈Ioo (-x) x := by
    rw [← habs y]
    have hiff : g x<g |y| ↔ |y|<x := by
      constructor
      · intro h
        by_contra! hn
        have hh := (P.green_strictAnti hs).antitoneOn
          (mem_Ici.mpr hx.le) (mem_Ici.mpr (abs_nonneg y)) hn
        exact (not_lt_of_ge hh) h
      · intro h
        exact P.green_strictAnti hs (mem_Ici.mpr (abs_nonneg y)) (mem_Ici.mpr hx.le) h
    exact hiff.trans abs_lt
  have hfun : (fun y => F (g y))=(Ioo (-x) x).indicator (fun _ => (1:ℝ)) := by
    funext y
    simp only [F,indicator_apply,hlevel]
  have hInt : Integrable (fun y => F (g y)) := by
    rw [hfun]
    exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioo
  have hleft : (∫ y,F (g y))=2*x := by
    rw [hfun,integral_indicator_const 1 measurableSet_Ioo,Real.volume_real_Ioo_of_le (by linarith : -x≤x)]
    simp only [smul_eq_mul,mul_one]
    ring
  have hquad := (P.green_quadrature hs F hInt).2
  have hlow : (1/2:ℝ)<g x := green_diagonal_strict P.density P.mass_pos hs P.pole x
  have hupp : g x<g 0 := P.green_strictAnti hs (by simp : (0:ℝ)∈Ici 0) (mem_Ici.mpr hx.le) hx
  have hF : (fun v => F v/sqrt (phase P.A P.edge v))=
      (Ioi (g x)).indicator (fun v => 1/sqrt (phase P.A P.edge v)) := by
    funext v
    by_cases hv : g x<v <;> simp [F,hv]
  have hset : Ioi (g x)∩Ioc (1/2:ℝ) (g 0)=Ioc (g x) (g 0) := by
    ext v
    constructor
    · intro hv
      exact ⟨hv.1,hv.2.2⟩
    · intro hv
      exact ⟨hv.1,hlow.trans hv.1,hv.2⟩
  have hright : (∫ v in (1/2:ℝ)..g 0,F v/sqrt (phase P.A P.edge v))=
      ∫ v in g x..g 0,1/sqrt (phase P.A P.edge v) := by
    rw [intervalIntegral.integral_of_le (hlow.trans hupp).le,hF,integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi,hset,intervalIntegral.integral_of_le hupp.le]
  change (∫ y,F (g y))=2*(∫ v in (1/2:ℝ)..g 0,F v/sqrt (phase P.A P.edge v)) at hquad
  rw [hleft,hright] at hquad
  have he : x=∫ v in g x..g 0,1/sqrt (phase P.A P.edge v) := by linarith
  exact ⟨intervalIntegral.intervalIntegrable_of_integral_ne_zero (by rw [← he]; exact hx.ne'),he⟩

/-- Every arbitrary physical candidate has the original inverse-phase definition, with genuine convergence, at every spatial point.
Use: completes the inverse-coordinate construction independently of an edge spectrum.
Article: jacobi, Appendix D.4.
Proof: the actual profile is even and has the printed turning height,
amplitude and switching level. Apply the proved positive-radius inverse
formula at |x| and rewrite its actual coefficients. At zero the integral
has equal endpoints and is genuinely integrable. -/
theorem candidate_inverse_phase {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) (x : ℝ) :
    let P := candidate s t c hs ht hc
    IntervalIntegrable (fun v => 1/sqrt (phase (amplitude t c) (edge t c) v)) volume
      (P.g hs.le x) (peak c) ∧
    |x|=∫ v in P.g hs.le x..peak c,1/sqrt (phase (amplitude t c) (edge t c) v) := by
  -- Positive and negative radii concern this same actual even Green profile.
  let P := candidate s t c hs ht hc
  have hn := candidate_normalization hs ht hc
  change P.A=amplitude t c ∧ P.edge=edge t c ∧ P.g hs.le 0=peak c at hn
  change IntervalIntegrable (fun v => 1/sqrt (phase (amplitude t c) (edge t c) v)) volume
      (P.g hs.le x) (peak c) ∧
    |x|=∫ v in P.g hs.le x..peak c,1/sqrt (phase (amplitude t c) (edge t c) v)
  by_cases hx : x=0
  · subst x
    rw [hn.2.2]
    exact ⟨by simp,by simp⟩
  · have h := P.inverse_phase hs (abs_pos.mpr hx)
    have habs : P.g hs.le |x|=P.g hs.le x := by
      rcases le_total 0 x with hxp | hxn
      · rw [abs_of_nonneg hxp]
      · rw [abs_of_nonpos hxn]
        exact (P.shape hs).2.2.1 x
    rwa [hn.1,hn.2.1,hn.2.2,habs] at h

end
end jacobi.Fredholm
