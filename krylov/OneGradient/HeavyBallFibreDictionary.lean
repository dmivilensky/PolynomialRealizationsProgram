import krylov.OneGradient.RawSpectralEndpoints
import krylov.Reference.HeavyBallCoefficients
import krylov.Reference.HeavyBallSpectralLimit
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), original physical small-coupling family.
Use: identify actual physical measured endpoints and the true Schur threshold
of the existing positive irreducible finite heavy-ball Jacobi matrices.
Source: original raw/physical completion dictionary, actual tridiagonal cross
column contraction and the genuine determinant-derived CG line lengths.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix chebyshev1 krylov.Reference krylov.Realization krylov.LinearAlgebra
variable {n : ℕ}

/-- Genuine first-site heavy-ball references have a nonzero initial gradient
and the full original physical gradient atom count in every positive dimension.
Use: all information-fibre domains are derived before their parameters are used.
Article: main_krylov, s5:fibre(b).
Proof: reuse actual raw CG nonstagnation and the full physical support dictionary. -/
theorem heavyBall_information_domains (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (n : ℕ) :
    WithLp.toLp 2 (JacobiData.site (n+1) 0)≠0 ∧
      (activeSpectralValues (heavyBallMatrix d q (n+1)) (heavyBallMatrix_posDef d q hd (n+1)).1
        (WithLp.toLp 2 (JacobiData.site (n+1) 0))).card=n+1 := by
  have hT := heavyBallMatrix_posDef d q hd (n+1)
  have ht := heavyBallMatrix_tridiagonal d q (n+1)
  have hn := heavyBallMatrix_adjacent_neg d q hd hq (n+1)
  exact ⟨raw_cg_nonstagnation _ hT ht hn 0 (by omega),raw_first_site_full_gradient_support _ hT ht hn⟩

/-- The actual leading principal block of the genuine heavy-ball family is
the shorter member with the same real parameters.
Use: the inverse endpoints use the true leading physical matrix.
Article: main_krylov, s5:fibre(b).
Proof: read the original entries at the actual cast-successor indices. -/
theorem heavyBall_last_leading (d q : ℝ) (n : ℕ) :
    lastLeading (heavyBallMatrix d q (n+2))=heavyBallMatrix d q (n+1) := by
  ext i j
  simp only [lastLeading,Matrix.submatrix_apply,heavyBallMatrix,Fin.castSucc_inj,Fin.val_castSucc]

/-- The genuine heavy-ball last cross-column contraction is its actual edge
squared times the final leading inverse entry, for every real test matrix.
Use: no artificial Schur data replace the actual physical family.
Article: main_krylov, s5:fibre(b).
Proof: the real tridiagonal cross-column theorem removes all earlier sites;
the remaining supplied edge is exactly minus d times q. -/
theorem heavyBall_last_cross_quadratic (d q : ℝ) (n : ℕ)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    lastCross (heavyBallMatrix d q (n+2)) ⬝ᵥ (M*ᵥ lastCross (heavyBallMatrix d q (n+2)))=
      (d*q)^2*M (Fin.last n) (Fin.last n) := by
  have hfar : ∀ i : Fin (n+1),i≠Fin.last n →
      heavyBallMatrix d q (n+2) (Fin.castSucc i) (Fin.last (n+1))=0 := by
    intro i hi
    apply heavyBallMatrix_tridiagonal
    left
    have hv : i.val≠n := by intro he;exact hi (Fin.ext he)
    simp only [Fin.val_castSucc,Fin.val_last]
    omega
  rw [tridiagonal_last_cross_quadratic _ hfar]
  have he : heavyBallMatrix d q (n+2) (Fin.castSucc (Fin.last n)) (Fin.last (n+1))= -d*q := by
    simp [heavyBallMatrix,Fin.ext_iff]
  rw [he]
  ring

/-- The original physical last-pivot Schur threshold of the genuine first-site
heavy-ball reference is d times the squared coupling.
Use: identify the actual information ratio, with its true measured denominator.
Article: main_krylov, s5:fibre(b).
Proof: the proved raw/physical normal gives the actual final diagonal, while
the genuine last CG length is the reciprocal constant LDL pivot. -/
theorem heavyBall_physical_schur_threshold (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (n : ℕ)
    (hg : WithLp.toLp 2 (JacobiData.site (n+2) 0)≠0)
    (hc : (activeSpectralValues (heavyBallMatrix d q (n+2)) (heavyBallMatrix_posDef d q hd (n+2)).1
      (WithLp.toLp 2 (JacobiData.site (n+2) 0))).card=n+2) :
    lastJacobiPivot _ (heavyBallMatrix_posDef d q hd (n+2)) _ hg hc-
      (lastInversePivot _ (heavyBallMatrix_posDef d q hd (n+2)) _ hg hc)⁻¹=d*q^2 := by
  rw [raw_last_lanczos_pivot _ _ (heavyBallMatrix_tridiagonal d q (n+2))
    (heavyBallMatrix_adjacent_neg d q hd hq (n+2)) hg hc,
    last_inverse_pivot_cg_length,heavyBall_cg_length d q hd hq (n+1) (by omega),inv_inv]
  simp only [heavyBallMatrix,ite_true,Fin.val_last,show n+1≠0 by omega,ite_false]
  ring

/-- Both original physical spectral endpoints of the genuine heavy-ball
reference equal the literal real-family Schur endpoint functions.
Use: the limiting ratio describes the original measured information fibre.
Article: main_krylov, s5:fibre(b).
Proof: identify physical completions with supplied diagonal updates, then
contract their actual last cross column in the genuine shorter leading block. -/
theorem heavyBall_physical_endpoint_formulas (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (n : ℕ)
    (hg : WithLp.toLp 2 (JacobiData.site (n+2) 0)≠0)
    (hc : (activeSpectralValues (heavyBallMatrix d q (n+2)) (heavyBallMatrix_posDef d q hd (n+2)).1
      (WithLp.toLp 2 (JacobiData.site (n+2) 0))).card=n+2)
    (mu upper : ℝ) (hlo : (heavyBallMatrix d q (n+1)-mu • 1).PosDef)
    (hhi : (upper • 1-heavyBallMatrix d q (n+1)).PosDef)
    (hband : (heavyBallMatrix d q (n+2)-mu • 1).PosSemidef ∧
      (upper • 1-heavyBallMatrix d q (n+2)).PosSemidef) :
    spectralLowerPivot _ (heavyBallMatrix_posDef d q hd (n+2)) _ hg hc mu=
      heavyBallLowerEndpoint d mu n q ∧
    spectralUpperPivot _ (heavyBallMatrix_posDef d q hd (n+2)) _ hg hc upper=
      heavyBallUpperEndpoint d upper n q := by
  have hL : (lastLeading (heavyBallMatrix d q (n+2))-mu • 1).PosDef := by
    rwa [heavyBall_last_leading]
  have hH : (upper • 1-lastLeading (heavyBallMatrix d q (n+2))).PosDef := by
    rwa [heavyBall_last_leading]
  obtain ⟨hl,hh⟩ := raw_physical_spectral_endpoint_formulas _ (heavyBallMatrix_posDef d q hd (n+2))
    (heavyBallMatrix_tridiagonal d q (n+2)) (heavyBallMatrix_adjacent_neg d q hd hq (n+2))
    hg hc mu upper hL hH hband
  rw [heavyBall_last_cross_quadratic,heavyBall_last_leading] at hl hh
  exact ⟨hl,hh⟩

/-- The actual original physical information ratio is exactly the real
heavy-ball family ratio, on its genuine spectral domain.
Use: transfer the proved limit to real full-atom physical information fibres.
Article: main_krylov, s5:fibre(b).
Proof: insert the actual two endpoint and Schur-threshold identities. -/
theorem heavyBall_physical_fibre_ratio (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (n : ℕ)
    (hg : WithLp.toLp 2 (JacobiData.site (n+2) 0)≠0)
    (hc : (activeSpectralValues (heavyBallMatrix d q (n+2)) (heavyBallMatrix_posDef d q hd (n+2)).1
      (WithLp.toLp 2 (JacobiData.site (n+2) 0))).card=n+2)
    (mu upper : ℝ) (hlo : (heavyBallMatrix d q (n+1)-mu • 1).PosDef)
    (hhi : (upper • 1-heavyBallMatrix d q (n+1)).PosDef)
    (hband : (heavyBallMatrix d q (n+2)-mu • 1).PosSemidef ∧
      (upper • 1-heavyBallMatrix d q (n+2)).PosSemidef) :
    let A := heavyBallMatrix d q (n+2)
    let hA := heavyBallMatrix_posDef d q hd (n+2)
    let g := WithLp.toLp 2 (JacobiData.site (n+2) 0)
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    (spectralUpperPivot A hA g hg hc upper-sigma)/(spectralLowerPivot A hA g hg hc mu-sigma)=
      heavyBallFibreRatio d mu upper n q := by
  obtain ⟨hl,hh⟩ := heavyBall_physical_endpoint_formulas d q hd hq n hg hc mu upper hlo hhi hband
  have hs := heavyBall_physical_schur_threshold d q hd hq n hg hc
  dsimp only
  rw [hl,hh,hs]
  rfl

end
end krylov.OneGradient
