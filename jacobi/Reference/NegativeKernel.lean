import jacobi.Reference.PositiveIntegral

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
After removing the exact endpoint power s^(gamma-1), the original
normalized sine density has a continuous strictly positive coefficient
on a compact rectangle away from the far singular endpoint. Its genuine
positive minimum supplies the uniform negative-energy lower bound.
Source: the removable sinc factor and the extreme value theorem.
Use: proves continuity and positivity of the original normalized density coefficient in betaDensityCoefficient_lower.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual scaled sinc is strictly positive before the first positive sine zero, including its removable endpoint value.
Use: proves continuity and positivity of the original normalized density coefficient in betaDensityCoefficient_lower.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the elementary removable extension sinc(0)=1 and positivity of sine on (0,pi).
Proof: handle the removable zero explicitly; at every other point the true sine quotient has a positive numerator and denominator. -/
theorem scaled_sinc_pos {s : ℝ} (hs : s∈Ico (0:ℝ) 1) : 0<Real.sinc (Real.pi*s) := by
  -- The original extension at zero, rather than a totalized zero quotient, gives the positive compact endpoint.
  by_cases h0 : s=0
  · simp [h0]
  have hp : 0<s := lt_of_le_of_ne hs.1 (Ne.symm h0)
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero h0)]
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hp)
    (by nlinarith [Real.pi_pos,hs.2])) (mul_pos Real.pi_pos hp)

/-- The true regular coefficient left after taking s^(gamma-1) out of the original normalized sine density.
Use: its positive compact minimum gives the actual negative-energy lower bound uniformly for spatial points bounded away from zero.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def betaDensityCoefficient (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*p.1)/Real.pi)^(1-gamma a)*
    (Real.sinc (Real.pi*p.2)*(Real.sin (Real.pi*(p.1-p.2))/Real.pi))^(gamma a-1)

/-- The actual density coefficient is strictly positive on its full physical regular region, including s=0.
Use: supplies the positive minimum on the compact rectangle in betaDensityCoefficient_lower.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the original beta normalization, both physical sine factors and the removable sinc factor are all strictly positive. -/
theorem betaDensityCoefficient_pos {a t s : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1)
    (hs : s∈Ico (0:ℝ) t) : 0<betaDensityCoefficient a (t,s) := by
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hts : t-s∈Ioo (0:ℝ) 1 := ⟨sub_pos.mpr hs.2,by linarith [ht.2,hs.1]⟩
  exact mul_pos (mul_pos (inv_pos.mpr (betaNormalization_pos hg))
    (Real.rpow_pos_of_pos (div_pos (sine_pos ht) Real.pi_pos) _))
      (Real.rpow_pos_of_pos (mul_pos (scaled_sinc_pos ⟨hs.1,hs.2.trans ht.2⟩)
        (div_pos (sine_pos hts) Real.pi_pos)) _)

/-- The original normalized sine density factors exactly into its singular endpoint power and the actual continuous coefficient.
Use: turns the positive compact coefficient bound into an integrable power lower bound in wave_imaginary_lower.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: sin(pi*s)/pi=s*sinc(pi*s) exactly. Factor the real power
at its genuinely positive bases and retain the original outside
beta normalization without any asymptotic substitution. -/
theorem betaDensityCoefficient_identity (a : ℝ) {t s : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hs : s∈Ioo (0:ℝ) t) :
    (betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)*sineWeight (gamma a) t s=
      s^(gamma a-1)*betaDensityCoefficient a (t,s) := by
  -- Factoring only at an interior integration point avoids every singular endpoint cancellation.
  have hp := mul_pos (scaled_sinc_pos ⟨hs.1.le,hs.2.trans ht.2⟩)
    (div_pos (sine_pos (show t-s∈Ioo (0:ℝ) 1 from ⟨sub_pos.mpr hs.2,by linarith [ht.2,hs.1]⟩)) Real.pi_pos)
  have he : Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2=
      s*(Real.sinc (Real.pi*s)*(Real.sin (Real.pi*(t-s))/Real.pi)) := by
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hs.1.ne')]
    field_simp [Real.pi_ne_zero,hs.1.ne']
  rw [sineWeight,he,Real.mul_rpow hs.1.le hp.le]
  dsimp [betaDensityCoefficient]
  ring

/-- The genuine regular density coefficient has one strictly positive lower bound over the complete compact spatial rectangle needed by the article.
Use: proves the uniform negative-energy lower estimate for every A<=t<=1/2, using 0<=s<=A/2 in the original integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the extreme value theorem for a continuous strictly positive function on a compact set.
Proof: every sine or sinc base is strictly positive on the compact
rectangle. Its real-power coefficient is continuous there, so the
community compact minimum theorem gives a genuinely positive minimum. -/
theorem betaDensityCoefficient_lower {a A : ℝ} (ha : -1<a) (hA : A∈Ioc (0:ℝ) (1/2)) :
    ∃ m : ℝ,0<m ∧ ∀ t∈Icc A (1/2),∀ s∈Icc (0:ℝ) (A/2),m≤betaDensityCoefficient a (t,s) := by
  -- The rectangle includes s=0 through the actual removable sinc extension; the opposite sine remains away from zero.
  let S := Icc A (1/2:ℝ) ×ˢ Icc (0:ℝ) (A/2)
  have hregion {p : ℝ × ℝ} (hp : p∈S) : p.1∈Ioo (0:ℝ) 1 ∧ p.2∈Ico (0:ℝ) p.1 := by
    exact ⟨⟨hA.1.trans_le hp.1.1,by linarith [hp.1.2]⟩,
      ⟨hp.2.1,by linarith [hp.2.2,hp.1.1,hA.1]⟩⟩
  have hc : ContinuousOn (betaDensityCoefficient a) S := by
    intro p hp
    obtain ⟨ht,hs⟩ := hregion hp
    have hbase : 0<Real.sinc (Real.pi*p.2)*(Real.sin (Real.pi*(p.1-p.2))/Real.pi) :=
      mul_pos (scaled_sinc_pos ⟨hs.1,hs.2.trans ht.2⟩)
        (div_pos (sine_pos ⟨sub_pos.mpr hs.2,by linarith [ht.2,hs.1]⟩) Real.pi_pos)
    have htbase : 0<Real.sin (Real.pi*p.1)/Real.pi := div_pos (sine_pos ht) Real.pi_pos
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Real.sin (Real.pi*q.1)/Real.pi) p := by fun_prop
    have h2 : ContinuousAt (fun q : ℝ × ℝ =>
        Real.sinc (Real.pi*q.2)*(Real.sin (Real.pi*(q.1-q.2))/Real.pi)) p := by fun_prop
    exact ((continuousAt_const.mul (h1.rpow_const (Or.inl htbase.ne'))).mul
      (h2.rpow_const (Or.inl hbase.ne'))).continuousWithinAt
  obtain ⟨m,hm,hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_forall_le' hc
    (fun p hp => betaDensityCoefficient_pos ha (hregion hp).1 (hregion hp).2)
  exact ⟨m,hm,fun t ht s hs => hmin (t,s) ⟨ht,hs⟩⟩

end
end jacobi.Reference
