import jacobi.Variational.FredholmCalculus
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual regularized Fredholm series is differentiable below its spectral
pole. A single summable bound controls the true logarithmic derivatives
through an open parameter interval containing zero and the given point.
This parameter variation is used to compare the spectral determinant with
its spatial Green-diagonal integral by equality of actual derivatives.
Source: mathlib's dominated differentiation theorem for series.
Use: differentiates the genuine convergent Fredholm spectral series below the pole.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set chebyshev2.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The scalar regularized logarithm has its exact derivative in the spectral parameter.
Use: differentiates the genuine convergent Fredholm spectral series below the pole.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: differentiate the actual logarithmic formula and clear its strictly positive denominator. -/
theorem fredholmLog_parameter_hasDerivAt {t a : ℝ} (hp : t*a<1) :
    HasDerivAt (fun u => fredholmLog u a) (t*a^2/(1-t*a)) t := by
  have hd := (((hasDerivAt_id t).mul_const a).const_sub 1).log (sub_pos.mpr hp).ne'
  have h := hd.neg.sub ((hasDerivAt_id t).mul_const a)
  convert h using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [(sub_pos.mpr hp).ne']
    ring

/-- The actual regularized Fredholm series has its genuine below-pole derivative in its parameter.
Use: gives the spectral side of the spatial determinant integral identity, including the zero-parameter endpoint.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: choose a slightly larger strictly subcritical positive parameter b.
On (-b,b), every logarithmic derivative is bounded by (b/epsilon)*lambda².
The square spectrum is summable and the series is zero at parameter zero;
mathlib's dominated series differentiation therefore gives the actual derivative. -/
theorem L1Source.fredholmReal_hasDerivAt (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    HasDerivAt (m.fredholmReal) (∑' n,s*m.spectrum n^2/(1-s*m.spectrum n)) s := by
  -- A slightly enlarged actual spectral margin controls a whole open parameter neighborhood.
  let Λ := observe m .top
  have hΛ : 0≤Λ := (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 0
  let b := s+(1-s*Λ)/(2*(Λ+1))
  have hbs : s<b := by
    dsimp only [b]
    exact lt_add_of_pos_right s (div_pos (sub_pos.mpr hp) (by positivity))
  have hb : 0<b := lt_of_le_of_lt hs hbs
  have hbmargin : b*Λ<1 := by
    have he : 2*(Λ+1)*(b-s)=1-s*Λ := by dsimp only [b]; field_simp; ring
    have hstep : 0≤b-s := sub_nonneg.mpr hbs.le
    nlinarith
  let ε := 1-b*Λ
  have hε : 0<ε := sub_pos.mpr hbmargin
  have hn (n : ℕ) : 0≤m.spectrum n := (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg n
  have htop (n : ℕ) : m.spectrum n≤Λ :=
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_antitone (Nat.zero_le n)
  have hmargin (t : ℝ) (ht : t∈Ioo (-b) b) (n : ℕ) : ε≤1-t*m.spectrum n := by
    have h₁ := mul_le_mul_of_nonneg_right ht.2.le (hn n)
    have h₂ := mul_le_mul_of_nonneg_left (htop n) hb.le
    dsimp only [ε]
    linarith
  have hsum := jacobi.Continuum.summable_powers
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable hn (by decide : 0<2)
  have hbound (n : ℕ) (t : ℝ) (ht : t∈Ioo (-b) b) :
      ‖t*m.spectrum n^2/(1-t*m.spectrum n)‖≤(b/ε)*m.spectrum n^2 := by
    have hden : 0<1-t*m.spectrum n := hε.trans_le (hmargin t ht n)
    have habs : |t|≤b := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_pow,abs_of_nonneg (hn n),abs_of_pos hden]
    calc
      _ ≤ b*m.spectrum n^2/(1-t*m.spectrum n) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right habs (sq_nonneg _)) hden.le
      _ ≤ b*m.spectrum n^2/ε :=
        div_le_div_of_nonneg_left (by positivity) hε (hmargin t ht n)
      _ = _ := by ring
  have h := hasDerivAt_tsum_of_isPreconnected (hsum.mul_left (b/ε)) isOpen_Ioo isPreconnected_Ioo
    (fun n t ht => fredholmLog_parameter_hasDerivAt (by have hh := hmargin t ht n; linarith)) hbound
    (show (0:ℝ)∈Ioo (-b) b by constructor <;> linarith)
    (by simpa only [fredholmLog,mul_zero,zero_mul,sub_zero,log_one,neg_zero] using
      (summable_zero : Summable (fun _ : ℕ => (0:ℝ))))
    (show s∈Ioo (-b) b by constructor <;> linarith)
  exact h

end
end jacobi.Variational
