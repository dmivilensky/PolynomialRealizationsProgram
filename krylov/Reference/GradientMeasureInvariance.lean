import krylov.Reference.CGMomentInvariance
import krylov.Reference.GradientMeasure
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b,c), actual spectral-measure CG invariance.
Use: identify genuine measured CG coefficients for any original physical reference having the same true normalized gradient spectral measure.
Source: actual finite aggregated spectral probability, proved physical polynomial Gram identity and genuine CG moment invariance.
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial
open scoped BigOperators
variable {n p : ℕ}

/-- Integration against the actual normalized finite gradient spectral probability of the original physical reference.
Use: Integration against the actual normalized finite gradient spectral probability of the original physical reference.
Article: main_krylov, prop:phi(b,c), actual spectral-measure CG invariance.
Proof: Sum over its genuine distinct active eigenvalues with their actual positive probability masses. -/
def gradientSpectralIntegral (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (f : ℝ → ℝ) : ℝ :=
  ∑ i,(gradientSpectralData base hb g hg).weight i*f ((gradientSpectralData base hb g hg).node i)

/-- The genuine normalized physical polynomial Gram is exactly its actual gradient spectral integral.
Use: The genuine normalized physical polynomial Gram is exactly its actual gradient spectral integral.
Article: main_krylov, prop:phi(b,c), actual spectral-measure CG invariance.
Proof: Use the proved real gradient-measure polynomial inner-product formula and cancel the actual nonzero initial energy. -/
theorem normalizedPolynomialGram_spectral (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (r s : ℝ[X]) :
    CG.normalizedPolynomialGram (cgOperator base) g r s=
      gradientSpectralIntegral base hb g hg (fun t => r.eval t*s.eval t) := by
  rw [CG.normalizedPolynomialGram,gradientSpectralData_inner base hb g hg,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hg))]
  rw [jacobi.Finite.DiscreteMeasure.inner_evaluate]
  simp only [gradientSpectralIntegral,mul_assoc]

/-- Equal actual normalized gradient spectral measures give identical genuinely measured CG line and recurrence coefficients, including stopped tails.
Use: Equal actual normalized gradient spectral measures give identical genuinely measured CG line and recurrence coefficients, including stopped tails.
Article: main_krylov, prop:phi(b,c), actual spectral-measure CG invariance.
Proof: Turn genuine measure equality into actual normalized polynomial Gram equality and apply the proved original CG moment invariance. -/
theorem cg_coefficients_of_spectralIntegral (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (other : Matrix (Fin p) (Fin p) ℝ) (ho : other.PosDef)
    (h : EuclideanSpace ℝ (Fin p)) (hh : h≠0)
    (hmeasure : ∀ f,gradientSpectralIntegral base hb g hg f=gradientSpectralIntegral other ho h hh f) (k : ℕ) :
    CG.length (cgOperator base) g k=CG.length (cgOperator other) h k ∧
      CG.beta (cgOperator base) g k=CG.beta (cgOperator other) h k := by
  apply CG.coefficients_of_normalizedGram _ _ _ _ hg hh
  intro r s
  rw [normalizedPolynomialGram_spectral base hb g hg,normalizedPolynomialGram_spectral other ho h hh]
  exact hmeasure _

/-- Every genuine gradient spectral atom is an actual eigenvalue of the original physical matrix.
Use: Every genuine gradient spectral atom is an actual eigenvalue of the original physical matrix.
Article: main_krylov, prop:phi(b,c), actual spectral-measure CG invariance.
Proof: Read the actual active-eigenvalue enumeration and its genuine image witness. -/
theorem gradientSpectralData_node_eigenvalue (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0)
    (i : Fin (activeSpectralValues base hb.1 g).card) :
    ∃ j : Fin n,hb.1.eigenvalues j=(gradientSpectralData base hb g hg).node i := by
  let F := activeSpectralValues base hb.1 g
  have ht : (F.equivFin.symm i).val∈F := (F.equivFin.symm i).property
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ht
  exact ⟨j,hj⟩
end
end krylov.Reference
