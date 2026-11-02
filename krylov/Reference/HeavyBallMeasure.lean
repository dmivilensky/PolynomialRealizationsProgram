import krylov.Reference.HeavyBallOrientation
import krylov.Reference.HeavyBallParameters
import krylov.Reference.HeavyBallCoefficients
import krylov.Reference.GradientMeasureInvariance
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Use: construct the printed positive-edge first-site spectral measure and derive genuine heavy-ball CG coefficients for every original reference having that same actual probability measure.
Source: genuine positive-edge matrix entries, actual finite spectral probability, strict true support and proved real CG spectral-moment invariance.
-/

namespace krylov.Reference
noncomputable section
open Matrix chebyshev1
open scoped BigOperators
variable {n N : ℕ}

/-- The actual genuine first physical basis vector used to define the original heavy-ball spectral measure.
Use: The actual genuine first physical basis vector used to define the original heavy-ball spectral measure.
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Proof: Use the true finite first-site coordinate vector. -/
def heavyBallInitial (N : ℕ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (JacobiData.site N 0)

/-- The actual first heavy-ball basis vector is nonzero in every genuine positive dimension.
Use: The actual first heavy-ball basis vector is nonzero in every genuine positive dimension.
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Proof: Its true initial physical coordinate is one. -/
theorem heavyBallInitial_ne_zero (N : ℕ) (hN : 0 < N) : heavyBallInitial N≠0 := by
  intro h
  have hh := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v ⟨0,hN⟩) h
  change (if (0:ℕ)=0 then (1:ℝ) else 0)=0 at hh
  norm_num at hh

/-- The original printed positive-edge finite heavy-ball Jacobi matrix.
Use: The original printed positive-edge finite heavy-ball Jacobi matrix.
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Proof: Use the actual pivot and negative of the genuine ratio in the physical three-diagonal constructor. -/
def heavyBallPositiveMatrix (I : SpectralInterval) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  heavyBallMatrix (HeavyBallParameters.pivot I) (-HeavyBallParameters.ratio I) N

/-- The actual positive-edge heavy-ball matrix has exactly the original printed first pivot, midpoint diagonal and positive quarter-width adjacent entries.
Use: The actual positive-edge heavy-ball matrix has exactly the original printed first pivot, midpoint diagonal and positive quarter-width adjacent entries.
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Proof: Substitute the genuine square-root pivot and coupling identities in every true physical matrix entry. -/
theorem heavyBallPositiveMatrix_entries (I : SpectralInterval) (N : ℕ) (i j : Fin N) :
    heavyBallPositiveMatrix I N i j=
      if i=j then if i.val=0 then HeavyBallParameters.pivot I else (I.L+I.mu)/2
      else if i.val+1=j.val ∨ j.val+1=i.val then (I.L-I.mu)/4 else 0 := by
  simp only [heavyBallPositiveMatrix,heavyBallMatrix,neg_sq,neg_mul_neg,
    HeavyBallParameters.diagonal,HeavyBallParameters.edge]

/-- The original printed heavy-ball matrix is genuinely positive definite.
Use: The original printed heavy-ball matrix is genuinely positive definite.
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Proof: Use its actual constant positive-pivot Gram factorization. -/
theorem heavyBallPositiveMatrix_posDef (I : SpectralInterval) (N : ℕ) :
    (heavyBallPositiveMatrix I N).PosDef :=
  heavyBallMatrix_posDef _ _ (HeavyBallParameters.pivot_pos I) N

/-- Integration against the actual normalized spectral probability of the printed heavy-ball matrix at its genuine first basis vector.
Use: Integration against the actual normalized spectral probability of the printed heavy-ball matrix at its genuine first basis vector.
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Proof: Construct the true finite gradient spectral measure of the original positive-edge matrix. -/
def heavyBallSpectralIntegral (I : SpectralInterval) (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) : ℝ :=
  gradientSpectralIntegral (heavyBallPositiveMatrix I N) (heavyBallPositiveMatrix_posDef I N)
    (heavyBallInitial N) (heavyBallInitial_ne_zero N hN) f

/-- Every actual atom of the original heavy-ball first-site spectral measure lies strictly between the genuine mu and L.
Use: Every actual atom of the original heavy-ball first-site spectral measure lies strictly between the genuine mu and L.
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Proof: Every real atom is a true matrix eigenvalue; actual alternating conjugacy and original square-root endpoint identities give its strict support. -/
theorem heavyBall_measure_support (I : SpectralInterval) (N : ℕ) (hN : 0 < N)
    (i : Fin (activeSpectralValues (heavyBallPositiveMatrix I N) (heavyBallPositiveMatrix_posDef I N).1
      (heavyBallInitial N)).card) :
    (gradientSpectralData (heavyBallPositiveMatrix I N) (heavyBallPositiveMatrix_posDef I N)
      (heavyBallInitial N) (heavyBallInitial_ne_zero N hN)).node i∈Set.Ioo I.mu I.L := by
  obtain ⟨j,hj⟩ := gradientSpectralData_node_eigenvalue (heavyBallPositiveMatrix I N)
    (heavyBallPositiveMatrix_posDef I N) (heavyBallInitial N) (heavyBallInitial_ne_zero N hN) i
  have h := heavyBall_positive_spectral_window _ _ (HeavyBallParameters.pivot_pos I)
    (HeavyBallParameters.ratio_domain I).1 (HeavyBallParameters.ratio_domain I).2.le N j
  rw [HeavyBallParameters.lower_endpoint,HeavyBallParameters.upper_endpoint] at h
  rw [← hj]
  exact h

/-- Every genuine original reference with the actual heavy-ball gradient spectral measure has exactly the printed measured CG line, internal recurrence and terminating coefficients.
Use: Every genuine original reference with the actual heavy-ball gradient spectral measure has exactly the printed measured CG line, internal recurrence and terminating coefficients.
Article: main_krylov, prop:phi(b), actual original heavy-ball spectral measure.
Proof: Transfer actual CG coefficients through genuine spectral-measure equality, then through the real first-site-preserving alternating isometry to the actual determinant-derived heavy-ball pivots. -/
theorem heavyBall_measure_coefficients (I : SpectralInterval) (hN : 0 < N)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0)
    (hmeasure : ∀ f,gradientSpectralIntegral base hb g hg f=heavyBallSpectralIntegral I N hN f)
    (k : ℕ) (hk : k<N) :
    CG.length (cgOperator base) g k=(HeavyBallParameters.pivot I)⁻¹ ∧
      (k+1<N → CG.beta (cgOperator base) g k=(HeavyBallParameters.ratio I)^2) ∧
      (k+1=N → CG.beta (cgOperator base) g k=0) := by
  -- Equality of the actual normalized spectral measures first identifies the true computed coefficients; only then change the genuine Jacobi orientation.
  let d := HeavyBallParameters.pivot I
  let q := HeavyBallParameters.ratio I
  have hm := cg_coefficients_of_spectralIntegral base hb g hg (heavyBallPositiveMatrix I N)
    (heavyBallPositiveMatrix_posDef I N) (heavyBallInitial N) (heavyBallInitial_ne_zero N hN) hmeasure k
  have ho := heavyBall_orientation_coefficients d q N k
  change CG.length (cgOperator (heavyBallPositiveMatrix I N)) (heavyBallInitial N) k=
    CG.length (cgOperator (heavyBallMatrix d q N)) (heavyBallInitial N) k ∧
    CG.beta (cgOperator (heavyBallPositiveMatrix I N)) (heavyBallInitial N) k=
    CG.beta (cgOperator (heavyBallMatrix d q N)) (heavyBallInitial N) k at ho
  refine ⟨?_,?_,?_⟩
  · exact hm.1.trans (ho.1.trans (heavyBall_cg_length d q (HeavyBallParameters.pivot_pos I)
      (HeavyBallParameters.ratio_domain I).1 k hk))
  · intro hint
    exact hm.2.trans (ho.2.trans (heavyBall_cg_beta_internal d q (HeavyBallParameters.pivot_pos I)
      (HeavyBallParameters.ratio_domain I).1 k hint))
  · intro hlast
    exact hm.2.trans (ho.2.trans (heavyBall_cg_beta_terminal d q (HeavyBallParameters.pivot_pos I)
      (HeavyBallParameters.ratio_domain I).1 k hlast))
end
end krylov.Reference
