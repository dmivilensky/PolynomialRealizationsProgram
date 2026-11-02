import jacobi.Bessel.Series
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Article: jacobi, Lemma 1.3.
The first normalized coefficients and the genuine central spectral
derivative are proved from the actual convergent entire function. The
coefficient recurrence is also expressed as the normalized Bessel
differential-equation coefficient identity for every degree.
Source: DLMF 10.2.2 and the proved mathlib hypergeometric power series.
Use: fixes the normalization for zero enumeration, the differential equation and canonical product.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Set Filter
open scoped Nat Topology
set_option backward.isDefEq.respectTransparency false

/-- The zeroth coefficient of the actual normalized Bessel series is one in the stated order range.
Use: fixes the normalization for zero enumeration, the differential equation and canonical product.
Article: jacobi, Lemma 1.3.
Proof: its factorial is one and its two nonzero Gamma factors cancel. -/
theorem coefficient_zero {a : ℂ} (ha : -1<a.re) : coefficient a 0=1 := by
  have hg : Gamma (a+1)≠0 := by simpa only [Nat.cast_zero,add_zero] using (order_nonzero ha 0).2
  simp [coefficient_formula,hg]

/-- The exact first spectral coefficient of the normalized entire Bessel function.
Use: its canonical-product comparison yields the first Rayleigh sum.
Article: jacobi, Lemma 1.3.
Proof: apply the genuine coefficient recurrence to the normalized constant term. -/
theorem coefficient_one {a : ℂ} (ha : -1<a.re) : coefficient a 1=-1/(4*(a+1)) := by
  simpa only [Nat.cast_zero,zero_add,add_zero,mul_one,coefficient_zero ha] using coefficient_succ ha 0

/-- The exact second spectral coefficient of the normalized entire Bessel function.
Use: comparison with the canonical product gives the second Rayleigh sum.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: use the actual recurrence at degree one and the proved first
coefficient, then collect the two positive-order denominator factors. -/
theorem coefficient_two {a : ℂ} (ha : -1<a.re) :
    coefficient a 2=1/(32*(a+1)*(a+2)) := by
  rw [show (2:ℕ)=1+1 by rfl,coefficient_succ ha 1,coefficient_one ha]
  norm_num only [Nat.cast_one]
  field_simp
  ring

/-- The true coefficients satisfy every coefficient equation of the normalized spectral Bessel ODE.
Use: supplies the complete algebraic recurrence for proving the actual differential equation by analytic series uniqueness.
Article: jacobi, Lemma 1.3.
Proof: multiply the proved recurrence by its nonzero actual factorial and shifted-order factors. -/
theorem coefficient_equation {a : ℂ} (ha : -1<a.re) (n : ℕ) :
    4*(n+1)*(a+1+n)*coefficient a (n+1)+coefficient a n=0 := by
  rw [coefficient_succ ha]
  have hn : (n:ℂ)+1≠0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp [hn,(order_nonzero ha n).1]
  ring

/-- The actual normalized entire function has its precise first spectral derivative at zero.
Use: connects the first Rayleigh coefficient to an ordinary derivative of the genuine function.
Article: jacobi, Lemma 1.3.
Proof: infinite convergence radius gives the actual hypergeometric power
series at zero. Its first coefficient is the genuine derivative there.
Apply the linear argument and constant Gamma normalization, retaining the exact scale -1/4. -/
theorem normalized_hasDerivAt_zero {a : ℂ} (ha : -1<a.re) :
    HasDerivAt (normalized a) (-1/(4*(a+1))) 0 := by
  -- The derivative comes from the existing convergent power series, rather than a formal coefficient calculation.
  let p := regularizedHGFunSeries (0:Multiset ℂ) {a+1}
  have hp : 0<p.radius := by rw [show p.radius=⊤ from radius a]; exact ENNReal.zero_lt_top
  have h := (p.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt.hasDerivAt
  have he : p 1 (fun _ => 1)=regularizedHGFunCoeff 0 {a+1} 1 := by
    simp [p,regularizedHGFunSeries]
  rw [he] at h
  have harg : HasDerivAt (fun z : ℂ => -z/4) (-1/4) 0 := by
    simpa only [Pi.neg_apply,id_eq] using ((hasDerivAt_id (0:ℂ)).neg).div_const 4
  have h' : HasDerivAt p.sum (regularizedHGFunCoeff 0 {a+1} 1) (-0/4) := by
    simpa only [neg_zero,zero_div] using h
  have hc := (h'.comp (0:ℂ) harg).const_mul (Gamma (a+1))
  have hec : Gamma (a+1)*(regularizedHGFunCoeff 0 {a+1} 1*(-1/4))=coefficient a 1 := by
    unfold coefficient
    ring
  rw [hec,coefficient_one ha] at hc
  exact hc

/-- The actual normalized Bessel function has no zeros in a genuine complex neighborhood of the origin.
Use: starts positive-zero enumeration away from the removable normalized origin.
Article: jacobi, Lemma 1.3.
Proof: the genuine entire function is continuous at zero and its proved
value there is one; continuity preserves nonvanishing in a neighborhood. -/
theorem normalized_eventually_ne_zero {a : ℂ} (ha : -1<a.re) :
    ∀ᶠ z in 𝓝 (0:ℂ),normalized a z≠0 := by
  have hn : normalized a 0≠0 := by rw [normalized_zero ha]; exact one_ne_zero
  exact (normalized_analytic a 0).continuousAt.eventually_ne hn

end
end jacobi.Bessel
