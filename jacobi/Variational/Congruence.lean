import jacobi.Variational.FredholmSpectrum

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
All actual integral and spectral observations are invariant under changes
on null sets. Equality classification can therefore use continuous canonical
representatives while every theorem still concerns the original density.
Source: Lebesgue integral congruence and the proved L1 spectral stability.
Use: KKT profiles acquire classical Green regularity without adding regularity assumptions to the original minimizer.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Filter chebyshev2.Continuum
set_option backward.isDefEq.respectTransparency false

/-- Replace an actual density by a nonnegative measurable almost-everywhere equal representative.
Use: KKT profiles acquire classical Green regularity without adding regularity assumptions to the original minimizer.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
-/
def Density.replace (m : Density) (f : ℝ → ℝ) (hf : Measurable f) (hn : ∀ x,0≤f x)
    (he : m.value=ᵐ[volume] f) : Density where
  value := f
  measurable := hf
  nonneg := hn
  integrable := m.integrable.congr he
  energy_integrable := m.energy_integrable.congr (he.fun_comp (fun r : ℝ => r^(3/2:ℝ)))

/-- Almost-everywhere equal densities have zero actual L1 distance.
Use: transfers the actual spectrum and all derived constraints between representatives.
Article: jacobi, Theorem D.5.
Proof: the absolute difference is zero almost everywhere, so its integral is zero. -/
theorem Density.l1_eq_zero_of_ae_eq {m q : Density} (h : m.value=ᵐ[volume] q.value) :
    (∫ x, |m.value x-q.value x|)=0 := by
  have hz : (fun x => |m.value x-q.value x|)=ᵐ[volume] (0 : ℝ → ℝ) :=
    h.mono fun x hx => by simp only [hx,sub_self,abs_zero,Pi.zero_apply]
  simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae hz

/-- Null-set changes preserve the actual mass.
Use: applies the explicit equality-family mass to every measurable equality density.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: apply Bochner integral congruence to the literal density functions. -/
theorem Density.mass_congr {m q : Density} (h : m.value=ᵐ[volume] q.value) : m.mass=q.mass :=
  integral_congr_ae h

/-- Null-set changes preserve the actual finite energy.
Use: all equality and calibration conclusions concern the original density.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: compose the density equality with the fixed 3/2 power and integrate. -/
theorem Density.energy_congr {m q : Density} (h : m.value=ᵐ[volume] q.value) : m.energy=q.energy :=
  integral_congr_ae (h.fun_comp (fun r : ℝ => r^(3/2 : ℝ)))

/-- Null-set changes preserve the complete actual ordered spectrum.
Use: transfers every observation between the measurable density and its canonical representative.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: L1 spectral stability gives zero total spectral distance, which bounds each entry difference. -/
theorem Density.spectrum_congr {m q : Density} (h : m.value=ᵐ[volume] q.value) : m.spectrum=q.spectrum := by
  -- Zero distance identifies entries, with multiplicities and zero padding retained.
  have hd := kernel_distance m.integrable q.integrable m.nonneg q.nonneg
  rw [Density.l1_eq_zero_of_ae_eq h] at hd
  funext n
  have he := entry_distance (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
    (kernelSpectralData q.integrable q.nonneg).eigenvalue_summable n
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (he.trans hd))

/-- Every spectral observation is invariant under null-set changes.
Use: transfers sharp Young equality from the literal translated family to arbitrary representatives.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: substitute the complete spectral identity in each of the two observation definitions. -/
theorem observe_congr {m q : Density} (h : m.value=ᵐ[volume] q.value) (i : Observation) :
    observe m i=observe q i := by
  cases i <;> simp only [observe,Density.spectrum_congr h]

end
end jacobi.Variational
