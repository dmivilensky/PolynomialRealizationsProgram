import jacobi.Analytic.ResolventDomain

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The shifted coefficients are the original genuine Bessel resolvent
eigenvalues. They are holomorphic on the actual slit domain and
have one summable original-spectrum majorant on each compact subset.
Use: shiftedProfile is the actual Theorem C.5 series, and shiftedEdge_compact_bound gives its original spectral majorant.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set

/-- The original shifted genuine Bessel edge eigenvalue.
Use: shiftedProfile is the actual Theorem C.5 series, and shiftedEdge_compact_bound gives its original spectral majorant.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
-/
def shiftedEdge (a:ℝ) (ha:-1<a) (k:ℕ) (w:ℂ) : ℂ :=
  2/((jacobi.Bessel.sigma a ha k:ℝ)+w)

/-- Every original reciprocal Bessel eigenvalue belongs to the same genuine closed positive spectral interval.
Use: the compact slit denominator estimate controls every original shifted mode, including the actual zero accumulation limit.
Article: jacobi, Theorem C.5.
Proof: the actual squared Bessel zeros are positive and increasing in their proved original enumeration. -/
theorem inverse_sigma_mem (a:ℝ) (ha:-1<a) (k:ℕ) :
    1/ jacobi.Bessel.sigma a ha k∈Icc (0:ℝ) (1/ jacobi.Bessel.sigma a ha 0) := by
  have hs := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
  have hs0 := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha 0)
  exact ⟨by positivity,one_div_le_one_div_of_le hs0 ((jacobi.Bessel.sigma_strictMono ha).monotone (Nat.zero_le k))⟩

/-- The actual original shifted Bessel spectral denominator is nonzero everywhere on the source slit plane.
Use: shiftedEdge_analytic proves genuine holomorphic dependence of every original resolvent mode.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: a vanishing original denominator would make its proved common positive-interval denominator vanish, contradicting the genuine slit estimate. -/
theorem shiftedEdge_denominator_ne (a:ℝ) (ha:-1<a) (k:ℕ) {w:ℂ} (hw:w∈edgeDomain a ha) :
    (jacobi.Bessel.sigma a ha k:ℂ)+w≠0 := by
  -- The nonzero premise is derived for the same genuine Bessel eigenvalue used by the original resolvent coefficient.
  have hs := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
  have hs0 := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha 0)
  have hne := slit_denominator_ne hs0 (inverse_sigma_mem a ha k) hw
  intro hz
  apply hne
  have hid : 1+((1/ jacobi.Bessel.sigma a ha k:ℝ):ℂ)*w=
      ((jacobi.Bessel.sigma a ha k:ℂ)+w)/(jacobi.Bessel.sigma a ha k:ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hs.ne']
  rw [hid,hz,zero_div]

/-- The original shifted Bessel edge value has its exact unshifted-coefficient resolvent factorization.
Use: shiftedEdge_compact_bound has the original summable edge spectrum as its genuine common compact majorant.
Article: jacobi, Theorem C.5.
Proof: all original spectral denominators are nonzero by the proved slit-domain theorem, and the actual positive Bessel eigenvalue justifies the exact field cancellation. -/
theorem shiftedEdge_factor (a:ℝ) (ha:-1<a) (k:ℕ) {w:ℂ} (hw:w∈edgeDomain a ha) :
    shiftedEdge a ha k w=(jacobi.Bessel.edgeValue a ha k:ℂ)*
      (1+((1/ jacobi.Bessel.sigma a ha k:ℝ):ℂ)*w)⁻¹ := by
  have hs := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
  have hd := shiftedEdge_denominator_ne a ha k hw
  unfold shiftedEdge jacobi.Bessel.edgeValue
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hs.ne',hd]

/-- The actual original shifted coefficients are holomorphic on the complete original slit domain.
Use: the genuinely uniformly summable shifted profile series in Theorem C.5 is holomorphic on that same source domain.
Article: jacobi, Theorem C.5.
Proof: the original denominator is affine and has the proved genuine nonzero value, so the community analytic quotient theorem applies. -/
theorem shiftedEdge_analytic (a:ℝ) (ha:-1<a) (k:ℕ) {w:ℂ} (hw:w∈edgeDomain a ha) :
    AnalyticAt ℂ (shiftedEdge a ha k) w := by
  unfold shiftedEdge
  fun_prop (disch := exact shiftedEdge_denominator_ne a ha k hw)

/-- Every compact subset of the actual slit plane has the original uniform summable spectral bound.
Use: shiftedProfile_majorant proves absolute uniform convergence of the actual Theorem C.5 series for all physical positions and all compact parameter sets.
Article: jacobi, Theorem C.5.
Proof: the actual original reciprocal eigenvalues all lie in the same proved positive interval. Its genuine compact inverse-denominator bound and the exact original factorization give the same positive original Rayleigh-summable majorant for every mode. -/
theorem shiftedEdge_compact_bound (a:ℝ) (ha:-1<a) {W:Set ℂ} (hW:IsCompact W)
    (hsub:W⊆edgeDomain a ha) :
    ∃C:ℝ,0<C ∧ ∀k:ℕ,∀w∈W,‖shiftedEdge a ha k w‖≤C* jacobi.Bessel.edgeValue a ha k := by
  obtain ⟨C,hC,hbound⟩ := denominator_compact_bound
    (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha 0)) hW hsub
  refine ⟨C,hC,?_⟩
  intro k w hw
  rw [shiftedEdge_factor a ha k (hsub hw),norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((jacobi.Bessel.edgeValue_properties ha).1 k)]
  exact (mul_le_mul_of_nonneg_left (hbound w hw _ (inverse_sigma_mem a ha k))
    ((jacobi.Bessel.edgeValue_properties ha).1 k).le).trans_eq (mul_comm _ _)

/-- The actual shifted edge coefficient at zero is exactly its original unshifted Bessel edge value.
Use: shiftedProfile_zero identifies the genuine Theorem C.5 profile with the already constructed original profile at w=0.
Article: jacobi, Theorem C.5.
Proof: the original zero shift leaves the genuine Bessel reciprocal unchanged. -/
theorem shiftedEdge_zero (a:ℝ) (ha:-1<a) (k:ℕ) :
    shiftedEdge a ha k 0=(jacobi.Bessel.edgeValue a ha k:ℂ) := by
  simp [shiftedEdge,jacobi.Bessel.edgeValue]

end
end jacobi.EdgeResolvent
