import krylov.OneGradient.PhysicalSpectralEndpoints
import krylov.OneGradient.JacobiCoupling
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), literal physical Gauss--Radau parameters.
Use: express both attained spectral endpoint pivots using the actual positive
last Jacobi coupling squared and actual shifted leading inverse entries.
Source: genuine full-atom Lanczos compression, actual tridiagonal cross-column
contraction and the proved original physical spectral interval theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra
variable {n : ℕ}

/-- The actual lower spectral Schur endpoint determined by the original known
leading Jacobi block and coupling column.
Use: construct the real lower completion rather than postulate a Radau measure.
Article: main_krylov, s5:fibre(b), b_minus. -/
def spectralLowerPivot
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (mu : ℝ) : ℝ :=
  let J := physicalJacobi A hA g hg hc
  let H := lastLeading J
  let x := lastCross J
  mu+x ⬝ᵥ ((H-mu • 1)⁻¹*ᵥ x)

/-- The actual upper spectral Schur endpoint of the same known physical information.
Use: construct its true upper endpoint completion with its real prescribed node.
Article: main_krylov, s5:fibre(b), b_plus. -/
def spectralUpperPivot
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (upper : ℝ) : ℝ :=
  let J := physicalJacobi A hA g hg hc
  let H := lastLeading J
  let x := lastCross J
  upper-x ⬝ᵥ ((upper • 1-H)⁻¹*ᵥ x)

/-- The actual final Jacobi coupling of a full-atom physical reference with
at least two active sites is strictly positive.
Use: prove the source's strict spectral information ratio, rather than merely
its non-strict relative-ball analogue.
Article: main_krylov, s5:fibre(b).
Proof: the genuine physical compression is the actual positively oriented
Lanczos multiplication matrix, whose adjacent positivity was already proved. -/
theorem physical_jacobi_last_coupling_positive
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+2) :
    0 < physicalJacobi A hA g hg hc (Fin.castSucc (Fin.last n)) (Fin.last (n+1)) := by
  rw [physicalJacobi,physical_lanczos_compression]
  exact lanczosVector_adjacent_pos A hA g hg _ _ rfl

/-- The real leading-to-last coupling column is nonzero for every actual
full-atom physical reference with at least two active sites.
Use: all strict inverse quadratic comparisons have a derived real nonzero vector.
Article: main_krylov, s5:fibre(b).
Proof: its actual final coordinate is the genuine strictly positive final Jacobi edge. -/
theorem physical_jacobi_last_cross_nonzero
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+2) :
    lastCross (physicalJacobi A hA g hg hc)≠0 := by
  intro he
  have hh := congrFun he (Fin.last n)
  change physicalJacobi A hA g hg hc (Fin.castSucc (Fin.last n)) (Fin.last (n+1))=0 at hh
  exact (physical_jacobi_last_coupling_positive A hA g hg hc).ne' hh

/-- Every actual inverse quadratic endpoint correction has the literal
beta-squared last-entry form, for any genuine leading matrix supplied to the contraction.
Use: reuse the same actual sparse coupling column for both shifted endpoint
inverses and the original positive threshold inverse.
Article: main_krylov, s5:fibre(b).
Proof: actual reconstructed tridiagonality identifies the cross column as the
positive last coupling times the genuine final leading coordinate vector. -/
theorem physical_jacobi_cross_quadratic
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+2)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    let J := physicalJacobi A hA g hg hc
    lastCross J ⬝ᵥ (M*ᵥ lastCross J)=
      J (Fin.castSucc (Fin.last n)) (Fin.last (n+1))^2*M (Fin.last n) (Fin.last n) := by
  apply tridiagonal_last_cross_quadratic
  intro i hi
  rw [physicalJacobi,physical_lanczos_jacobi,(gradientSpectralData A hA g hg).reconstructed_matrix]
  apply (gradientSpectralData A hA g hg).multiplication_tridiagonal
  left
  have hin : i.val < n := by
    have hi' : i.val≠n := by intro he;apply hi;exact Fin.ext he
    omega
  simpa only [Fin.val_castSucc,Fin.val_last] using (show i.val+1 < n+1 by omega)

/-- Both genuine physical endpoint pivots have exactly the source's printed
beta-squared shifted-leading-inverse formulas.
Use: the two actual matrix completions are in the article's literal positive
Jacobi coordinates, with no abstract endpoint quantities left to identify.
Article: main_krylov, s5:fibre(b), equations for b_minus and b_plus.
Proof: insert the actual singleton coupling-column contraction into each true
physical Schur endpoint definition. -/
theorem spectral_pivot_beta_formulas
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+2) (mu upper : ℝ) :
    let J := physicalJacobi A hA g hg hc
    let H := lastLeading J
    let beta := J (Fin.castSucc (Fin.last n)) (Fin.last (n+1))
    spectralLowerPivot A hA g hg hc mu=mu+beta^2*(H-mu • 1)⁻¹ (Fin.last n) (Fin.last n) ∧
      spectralUpperPivot A hA g hg hc upper=upper-beta^2*(upper • 1-H)⁻¹ (Fin.last n) (Fin.last n) := by
  constructor
  · unfold spectralLowerPivot
    dsimp only
    rw [physical_jacobi_cross_quadratic]
  · unfold spectralUpperPivot
    dsimp only
    rw [physical_jacobi_cross_quadratic]

/-- Both genuine physical spectral endpoints lie in the original closed
spectral class, and the actual endpoint interval is nonempty.
Use: all endpoint adversarial references exist as real physical matrices.
Article: main_krylov, s5:fibre(b).
Proof: the proved physical interval equivalence and one true feasible witness
give the endpoint order; substituting the actual lower and upper endpoints
then supplies both real whole spectral tests. -/
theorem spectral_fibre_endpoint_band
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (mu upper : ℝ)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let lo := spectralLowerPivot A hA g hg hc mu
    let hi := spectralUpperPivot A hA g hg hc upper
    lo≤hi ∧ ((lanczosCompletion A hA g hg hc lo-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion A hA g hg hc lo).PosSemidef) ∧
      ((lanczosCompletion A hA g hg hc hi-mu • 1).PosSemidef ∧
        (upper • 1-lanczosCompletion A hA g hg hc hi).PosSemidef) := by
  obtain ⟨horder,he⟩ := physical_spectral_fibre_interval A hA g hg hc mu upper hne
  exact ⟨horder,(he _).mpr ⟨le_rfl,horder⟩,(he _).mpr ⟨horder,le_rfl⟩⟩

/-- Every actually admitted positive-lower-band completion is genuinely positive definite.
Use: both physical Schur endpoints have actual inverse metrics and retain the
full original active atom count before their minimax and measure formulas are used.
Article: main_krylov, s5:fibre(b).
Proof: the actual lower shifted form is nonnegative and the true positive scalar
identity is positive; their exact sum is the original physical completion. -/
theorem spectral_fibre_completion_positive
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (mu b : ℝ) (hmu : 0 < mu)
    (hlo : (lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef) :
    (lanczosCompletion A hA g hg hc b).PosDef := by
  have hd : (mu • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)).PosDef := by
    rw [Matrix.smul_one_eq_diagonal,Matrix.posDef_diagonal_iff]
    exact fun _ => hmu
  simpa only [sub_add_cancel] using Matrix.PosDef.posSemidef_add hlo hd

end
end krylov.OneGradient
