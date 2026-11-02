import jacobi.Bessel.CanonicalProduct
import jacobi.Variational.Problem

/-!
Article: jacobi, Lemma 1.3.
The actual Bessel eigenvalues instantiate the already developed general
edge-spectrum interface. Both moments and the strict first-zero bound are
unconditional theorems about the genuine source special function.
Use: specializes the earlier arbitrary-spectrum machinery without repeating its operator or minimization proofs.
-/
namespace jacobi.Bessel
noncomputable section

/-- The actual Bessel edge spectrum, packaged for all general variational and Transfer theorems.
Use: specializes the earlier arbitrary-spectrum machinery without repeating its operator or minimization proofs.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def edgeSpectrum (a : ℝ) (ha : -1<a) : jacobi.Variational.EdgeSpectrum where
  value := edgeValue a ha
  positive := (edgeValue_properties ha).1
  antitone := (edgeValue_properties ha).2.antitone
  summable := edgeValue_summable ha

/-- The actual packaged Bessel spectrum has exactly the printed total mass.
Use: supplies the genuine mass constraint to every previously proved calibration.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: this is the proved first infinite Rayleigh sum for the actual spectrum. -/
theorem edgeSpectrum_mass {a : ℝ} (ha : -1<a) :
    (edgeSpectrum a ha).mass=1/(2*(a+1)) := first_rayleigh_sum ha

/-- The actual packaged Bessel spectrum has exactly the printed second moment.
Use: supplies the genuine second-moment constraint to the sharp Young and elliptic calibrations.
Article: jacobi, Lemma 1.3.
Proof: this is the proved second infinite Rayleigh sum, with the original edge eigenvalues. -/
theorem edgeSpectrum_second {a : ℝ} (ha : -1<a) :
    (edgeSpectrum a ha).second=1/(4*(a+1)^2*(a+2)) := second_rayleigh_sum ha

/-- The genuine Bessel shape ratio has its exact elementary value.
Use: determines the Young versus elliptic second-moment regime from the actual order alpha.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: substitute both proved moments; alpha+1 is strictly positive, justifying cancellation. -/
theorem edgeSpectrum_shape {a : ℝ} (ha : -1<a) :
    (edgeSpectrum a ha).second/(edgeSpectrum a ha).mass^2=1/(a+2) := by
  rw [edgeSpectrum_mass ha,edgeSpectrum_second ha]
  have h1 : a+1≠0 := by linarith
  have h2 : a+2≠0 := by linarith
  field_simp [h1,h2]
  norm_num

/-- The genuine first squared Bessel zero is strictly above 4*(alpha+1).
Use: guarantees the strict positive affine spectral gap needed in the near-edge interpolation estimate.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the positive second spectral entry makes the leading eigenvalue
strictly smaller than the exact total Rayleigh mass. Convert that strict
reciprocal inequality using the actual positive squared zero. -/
theorem first_zero_lower_bound {a : ℝ} (ha : -1<a) :
    4*(a+1)<sigma a ha 0 := by
  have h := (edgeSpectrum a ha).top_lt_mass
  rw [edgeSpectrum_mass ha] at h
  change 2/sigma a ha 0<1/(2*(a+1)) at h
  have hs := spectralZero_pos ha (sigma_mem ha 0)
  have hd : 0<2*(a+1) := by linarith
  have hh := (div_lt_div_iff₀ hs hd).mp h
  linarith

/-- Every actual squared Bessel zero lies strictly above the Liouville affine correction.
Use: discharges the fixed-index positive limit in Proposition B.1, including all alpha>-1.
Article: jacobi, Proposition B.1.
Proof: the first-zero Rayleigh bound holds for the whole increasing list.
The remaining scalar gap is positive throughout the full order range. -/
theorem sigma_above_correction {a : ℝ} (ha : -1<a) (k : ℕ) :
    (1/4:ℝ)-a^2<sigma a ha k := by
  have hf := first_zero_lower_bound ha
  have hm := sigma_strictMono ha |>.monotone (Nat.zero_le k)
  nlinarith [sq_nonneg (a+1)]

/-- The canonical product is genuinely convergent to the actual normalized entire function, including at its zeros.
Use: subsequent Fredholm identities may use HasProd rather than a totalized product without convergence evidence.
Article: jacobi, Lemma 1.3.
Proof: absolute summability of its true spectral perturbations gives
multipliability. The already proved canonical identity identifies its limit. -/
theorem canonical_product_hasProd {a : ℝ} (ha : -1<a) (z : ℂ) :
    HasProd (fun k => 1-z/(sigma a ha k:ℂ)) (normalized (a:ℂ) z) := by
  -- Absolute summability is established before interpreting the value of the total product.
  have h := multipliable_one_add_of_summable
    (complex_spectral_summable (-z/2) (edgeValue_summable ha)
      (fun k => ((edgeValue_properties ha).1 k).le))
  have he : (fun k => 1+(-z/2)*(edgeValue a ha k:ℂ))=
      fun k => 1-z/(sigma a ha k:ℂ) := by
    funext k
    unfold edgeValue
    push_cast
    ring
  rw [he] at h
  rw [canonical_product ha z]
  exact h.hasProd

/-- The normalized cylindrical Bessel product holds at every complex argument squared.
Use: recovers exactly the printed Weierstrass variable convention from the entire spectral coordinate.
Article: jacobi, Lemma 1.3.
Proof: substitute z squared in the proved actual product and use the exact squared-zero identification. -/
theorem cylindrical_canonical_product {a : ℝ} (ha : -1<a) (z : ℂ) :
    normalized (a:ℂ) (z^2)=∏' k:ℕ,(1-z^2/(positiveZero a ha k:ℂ)^2) := by
  rw [canonical_product ha (z^2)]
  apply tprod_congr
  intro k
  rw [← Complex.ofReal_pow,(positiveZero_properties ha k).2]

end
end jacobi.Bessel
