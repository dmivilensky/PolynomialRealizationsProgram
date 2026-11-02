import jacobi.RootMass.FirstIntegral
import jacobi.RootMass.Substitution
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
The actual optimizer state is an injective differentiable map from its
positive half-core onto the true turning interval. Its proved first integral
supplies the exact absolute Jacobian. Reflection gives the full compact-core
integral, and the already proved inverse substitution makes it nonsingular.
Source: actual Green conservation and the Lebesgue change-of-variables theorem.
Use: supplies injectivity and exact interval image in the genuine spatial substitution.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized state strictly decreases across its entire closed positive half-core.
Use: supplies injectivity and exact interval image in the genuine spatial substitution.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the proved actual branch derivative has the sign of the strictly negative radial Green slope throughout the interior. -/
theorem Profile.state_strictAnti {a b T : ℝ} (P : Profile a b T) (hb : 0<b) :
    StrictAntiOn P.state (Icc (0:ℝ) P.radius) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc (0:ℝ) P.radius) P.state_continuous.continuousOn
    (fun x hx => (P.state_hasDerivAt hb (by
      have hx' : x∈Ioo (0:ℝ) P.radius := by simpa only [interior_Icc] using hx
      rw [abs_of_pos hx'.1]; exact hx'.2.le)).hasDerivWithinAt)
  intro x hx
  have hx' : x∈Ioo (0:ℝ) P.radius := by simpa only [interior_Icc] using hx
  have hn := P.state_ge_one hb (by rw [abs_of_pos hx'.1]; exact hx'.2.le)
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (P.D_neg hb hx'.1)) (by nlinarith)

/-- The true spatial state maps its positive open half-core precisely onto the actual turning interval.
Use: the integration interval is the same constructed inverse interval as in the printed quadratures.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: continuity and actual strict decrease give the interval image; substitute the proved boundary and central values. -/
theorem Profile.state_image {a b T : ℝ} (P : Profile a b T) (ha : -2*sqrt 3<a) (hb : 0<b) :
    P.state '' Ioo (0:ℝ) P.radius=Ioo (1:ℝ) (inverse a ha P.y) := by
  have hh := P.state_continuous.continuousOn.image_Ioo_of_strictAntiOn P.radius_pos.le (P.state_strictAnti hb)
  rwa [P.state_boundary hb,P.peak ha hb] at hh

/-- The actual first integral selects the precise positive square root of the turning radicand.
Use: cancels the spatial Jacobian without an unproved branch selection.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the radicand is the square of nhat times C'; nhat>0 and the original radial slope is negative. -/
theorem Profile.sqrt_radicand {a b T : ℝ} (P : Profile a b T) (hb : 0<b)
    {x : ℝ} (hx : x∈Ioo (0:ℝ) P.radius) :
    sqrt (radicand a P.y (P.state x))= -(P.state x*P.D x) := by
  have hn := P.state_ge_one hb (by rw [abs_of_pos hx.1]; exact hx.2.le)
  have hd := P.D_neg hb hx.1
  have he : radicand a P.y (P.state x)=(-(P.state x*P.D x))^2 := by
    have hh := P.first_integral hb ⟨hx.1.le,hx.2.le⟩
    nlinarith
  rw [he,sqrt_sq (by nlinarith [mul_neg_of_pos_of_neg (zero_lt_one.trans_le hn) hd])]

/-- Every actual core state observable has the genuine printed turning-interval quadrature.
Use: evaluates all inner optimizer observables and therefore the exact root-mass lower bound.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: apply the actual spatial Jacobian theorem on the positive half-core.
The proved first integral cancels its derivative to 2*F. The observable
restricted to the symmetric core is even, so reflection doubles the half integral. -/
theorem Profile.quadrature {a b T : ℝ} (P : Profile a b T) (ha : -2*sqrt 3<a) (hb : 0<b)
    (F : ℝ → ℝ) :
    (∫ x in Ioo (-P.radius) P.radius,F (P.state x))=turningIntegral a ha P.y F := by
  -- The true profile, rather than a candidate formal ODE solution, supplies this Jacobian.
  let d (x : ℝ) := 2*P.state x^2*P.D x/(3*P.state x^2-1)
  have hder (x : ℝ) (hx : x∈Ioo (0:ℝ) P.radius) :
      HasDerivWithinAt P.state (d x) (Ioo (0:ℝ) P.radius) x :=
    (P.state_hasDerivAt hb (by rw [abs_of_pos hx.1]; exact hx.2.le)).hasDerivWithinAt
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder
    ((P.state_strictAnti hb).mono Ioo_subset_Icc_self).injOn
    (fun n => F n*(3*n^2-1)/(n*sqrt (radicand a P.y n)))
  rw [P.state_image ha hb] at hh
  have hj (x : ℝ) (hx : x∈Ioo (0:ℝ) P.radius) :
      |d x| *(F (P.state x)*(3*P.state x^2-1)/(P.state x*sqrt (radicand a P.y (P.state x))))=2*F (P.state x) := by
    have hn := P.state_ge_one hb (by rw [abs_of_pos hx.1]; exact hx.2.le)
    have hd := P.D_neg hb hx.1
    have hden : 0<3*P.state x^2-1 := by nlinarith
    have hdneg : d x<0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hd) hden
    rw [abs_of_neg hdneg,P.sqrt_radicand hb hx]
    dsimp only [d]
    field_simp
    ring_nf
    have hnon : -P.D x+P.D x*P.state x^2*3≠0 := by
      have hh := mul_ne_zero hd.ne hden.ne'
      convert hh using 1
      ring
    nlinarith [congrArg (fun r : ℝ => F (P.state x)*r) (mul_inv_cancel₀ hnon)]
  have hr : (∫ x in Ioo (0:ℝ) P.radius,|d x| •
      (F (P.state x)*(3*P.state x^2-1)/(P.state x*sqrt (radicand a P.y (P.state x)))))=
      2*(∫ x in Ioo (0:ℝ) P.radius,F (P.state x)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => by simpa only [smul_eq_mul] using hj x hx
  rw [hr] at hh
  let g (x : ℝ) := if |x|<P.radius then F (P.state x) else 0
  have habs (x : ℝ) : P.state |x|=P.state x := by
    rcases le_total 0 x with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn,P.state_even]
  have hfull : (∫ x,g x)=2*(∫ x in Ioi (0:ℝ),g x) := by
    simpa only [g,abs_abs,habs] using integral_comp_abs (f := g)
  have hg : (∫ x,g x)=∫ x in Ioo (-P.radius) P.radius,F (P.state x) := by
    rw [← integral_indicator measurableSet_Ioo]
    congr 1
    funext x
    simp only [g,indicator,abs_lt,mem_Ioo]
  have hhalf : (∫ x in Ioi (0:ℝ),g x)=∫ x in Ioo (0:ℝ) P.radius,F (P.state x) := by
    have he : (∫ x in Ioi (0:ℝ),g x)=∫ x in Ioi (0:ℝ),
        (Ioo (0:ℝ) P.radius).indicator (fun t => F (P.state t)) x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx' : 0<x := hx
      simp only [g,abs_of_pos hx',indicator,mem_Ioo,and_iff_right hx']
    rw [he,setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr Ioo_subset_Ioi_self]
  rw [hg,hhalf] at hfull
  exact hfull.trans hh.symm

end
end jacobi.RootMass
