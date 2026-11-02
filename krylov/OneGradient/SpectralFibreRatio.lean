import krylov.OneGradient.SpectralFibreParameters
import krylov.LinearAlgebra.InverseShiftQuadratic
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), strict spectral information ratio.
Use: prove the source's strict r < kappa for every genuine full-atom reference
with at least two sites, including collapsed physical completion intervals.
Source: actual irreducible last coupling, true positive leading forms and the
proved strict inverse quadratic variational comparison.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra
variable {n : ℕ}

/-- The actual spectral endpoint gaps lie strictly inside the original
positive spectral endpoints after subtraction of the genuine Schur threshold.
Use: strict irreducibility excludes equality in the one-gradient spectral
information ratio; no artificial lower-energy margin is assumed.
Article: main_krylov, s5:fibre(b).
Proof: the true last coupling column is nonzero. A positive downward leading
shift strictly increases its actual inverse quadratic form; the original and
upper-shift inverse quadratic forms are positive. Insert these real forms in
the literal physical Schur endpoint and threshold identities. -/
theorem spectral_fibre_endpoint_gaps
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+2) (mu upper : ℝ) (hmu : 0 < mu)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    mu < spectralLowerPivot A hA g hg hc mu-sigma ∧
      spectralUpperPivot A hA g hg hc upper-sigma < upper := by
  let J := physicalJacobi A hA g hg hc
  let H := lastLeading J
  let x := lastCross J
  have hH : H.PosDef := (physical_jacobi_positive A hA g hg hc).submatrix (Fin.castSucc_injective (n+1))
  have hx : x≠0 := physical_jacobi_last_cross_nonzero A hA g hg hc
  obtain ⟨b,hblo,hbhi⟩ := hne
  obtain ⟨hlo,hhi⟩ := physical_fibre_leading_strict A hA g hg hc mu upper b hblo hbhi
  have hstrict := shifted_inverse_quadratic_strict H hH mu hmu hlo x hx
  have hpos : 0 < x ⬝ᵥ (H⁻¹*ᵥ x) := by simpa only [star_trivial] using hH.inv.dotProduct_mulVec_pos hx
  have hupper : 0 < x ⬝ᵥ ((upper • 1-H)⁻¹*ᵥ x) := by
    simpa only [star_trivial] using hhi.inv.dotProduct_mulVec_pos hx
  have hsigma := physical_jacobi_schur_threshold A hA g hg hc
  change x ⬝ᵥ (H⁻¹*ᵥ x)=lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ at hsigma
  dsimp only
  rw [← hsigma]
  change mu < mu+x ⬝ᵥ ((H-mu • 1)⁻¹*ᵥ x)-x ⬝ᵥ (H⁻¹*ᵥ x) ∧
    upper-x ⬝ᵥ ((upper • 1-H)⁻¹*ᵥ x)-x ⬝ᵥ (H⁻¹*ᵥ x) < upper
  constructor <;> linarith

/-- Every original irreducible physical spectral information fibre has
strictly smaller last-CG-step ratio than the global condition ratio.
Use: the uniform spectral minimax coefficient is approached only by a limiting
family, and is never attained by a genuine full-atom reference.
Article: main_krylov, s5:fibre(b), r(I) < kappa.
Proof: the actual feasible endpoint interval is ordered, and its true pivot
gaps are strictly above mu and below upper. Their real positive quotient is
therefore strictly below upper/mu, with every denominator derived from the
original actual physical source data. -/
theorem spectral_fibre_ratio_strict
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+2) (mu upper : ℝ) (hmu : 0 < mu)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    (spectralUpperPivot A hA g hg hc upper-sigma)/
      (spectralLowerPivot A hA g hg hc mu-sigma) < upper/mu := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let lo := spectralLowerPivot A hA g hg hc mu
  let hi := spectralUpperPivot A hA g hg hc upper
  obtain ⟨hlo,hhi⟩ := spectral_fibre_endpoint_gaps A hA g hg hc mu upper hmu hne
  have horder : lo≤hi := (spectral_fibre_endpoint_band A hA g hg hc mu upper hne).1
  change mu < lo-sigma at hlo
  change hi-sigma < upper at hhi
  have hu : 0 < upper := by linarith
  dsimp only
  change (hi-sigma)/(lo-sigma) < upper/mu
  apply (div_lt_div_iff₀ (hmu.trans hlo) hmu).mpr
  have h1 := mul_lt_mul_of_pos_left hhi hmu
  have h2 := mul_lt_mul_of_pos_left hlo hu
  nlinarith

end
end krylov.OneGradient
