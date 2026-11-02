import krylov.LinearAlgebra.NormOrder
import chebyshev2.Continuum.FiniteTrace
import Mathlib.Tactic.NoncommRing

/-!
Article: main_krylov, apA:galerkin(e), trace/nuclear support.
Use: the finite-matrix nuclear norm is the previously proved actual finite-frame
nuclear norm, not an assumed list of eigenvalues or an unproved dual formula.
Source: Simon, Trace Ideals; reuse the earlier article's nuclearNorm_eigenbasis
and finite-dimensional trace-class theorem, together with the actual spectral basis.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace
variable {n : ℕ}

/-- The actual finite matrix nuclear norm, reusing the earlier finite-frame definition.
Use: the compressed uncertainty support is expressed in the same genuine nuclear norm.
Article: main_krylov, apA:galerkin(e), ‖PZP‖_*.
Source: chebyshev2.Continuum.nuclearNorm; finite matrices are already proved trace class. -/
def matrixNuclearNorm (K : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (chebyshev2.Continuum.nuclearNorm (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) K)).toReal

/-- The actual finite nuclear norm equals the sum of the absolute actual eigenvalues.
Use: compute the uncertainty support without introducing another nuclear-norm definition.
Article: main_krylov, apA:galerkin(e), finite spectral nuclear norm.
Proof: use the actual finite orthonormal eigenbasis and the earlier proved nuclear
eigenbasis formula; finite trace class discharges its finiteness hypothesis. -/
theorem matrixNuclearNorm_eq (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsHermitian) :
    matrixNuclearNorm K = ∑ i, |hK.eigenvalues i| := by
  -- The genuine finite eigenbasis is also a complete Hilbert basis for the existing norm theorem.
  let b := hK.eigenvectorBasis.toHilbertBasis
  have he : ∀ i, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) K (b i) =
      hK.eigenvalues i • b i := by
    intro i
    have hi : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) K (hK.eigenvectorBasis i) =
        hK.eigenvalues i • hK.eigenvectorBasis i := by
      ext j
      exact congrFun (hK.mulVec_eigenvectorBasis i) j
    simpa only [b, OrthonormalBasis.coe_toHilbertBasis] using hi
  have hn := (chebyshev2.Continuum.nuclearNorm_eigenbasis b
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) K) he
    (chebyshev2.Continuum.euclidean_isTraceClass _)).2
  rw [matrixNuclearNorm, hn, tsum_fintype, ENNReal.toReal_ofReal
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)]

/-- The real spectral sign keeps zero eigenvalues zero.
Use: a sign witness stays supported on the old subspace even at singular eigenvalues.
Article: main_krylov, apA:galerkin(e), sign(PZP). -/
def spectralSign (x : ℝ) : ℝ := if x = 0 then 0 else if 0 < x then 1 else -1

/-- The true scalar sign has magnitude at most one and pairs with its argument to give its absolute value.
Use: both the norm budget and the exact attaining trace of the sign witness.
Article: main_krylov, apA:galerkin(e).
Proof: split zero, positive and negative real arguments. -/
theorem spectralSign_properties (x : ℝ) : |spectralSign x| ≤ 1 ∧ spectralSign x * x = |x| := by
  by_cases hz : x = 0
  · simp [spectralSign, hz]
  · by_cases hp : 0 < x
    · simp [spectralSign, hz, hp, abs_of_pos hp]
    · have hm : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      simp [spectralSign, hz, hp, abs_of_neg hm]

/-- The actual spectral sign matrix in a proved orthogonal spectral basis.
Use: construct the supported nuclear-dual maximizing perturbation.
Article: main_krylov, apA:galerkin(e), sign(PZP). -/
def signInBasis {K : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis K) : Matrix (Fin n) (Fin n) ℝ :=
  B.Q * diagonal (fun i => spectralSign (B.eigenvalues i)) * B.Qᵀ

/-- The actual sign matrix has its prescribed scalar spectral coordinates.
Use: prove its trace, symmetry, budget and support by exact finite coordinate algebra.
Article: main_krylov, apA:galerkin(e).
Proof: cancel the genuine orthogonal change of basis on each side of the sign diagonal. -/
theorem coordinates_sign {K : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis K) :
    B.coordinates (signInBasis B) = diagonal (fun i => spectralSign (B.eigenvalues i)) := by
  unfold SpectralBasis.coordinates signInBasis
  simp only [← Matrix.mul_assoc, B.transpose_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, B.transpose_mul, Matrix.mul_one]

/-- The constructed matrix sign is genuinely symmetric.
Use: the actual attaining perturbation belongs to the symmetric uncertainty class.
Article: main_krylov, apA:galerkin(e).
Proof: transpose its real diagonal orthogonal congruence. -/
theorem signInBasis_isSymm {K : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis K) :
    (signInBasis B).IsSymm := by
  simp only [signInBasis, Matrix.IsSymm, transpose_mul, transpose_transpose,
    diagonal_transpose, Matrix.mul_assoc]

/-- Orthogonal spectral coordinates preserve the actual matrix trace.
Use: compute the uncertainty pairing in the eigenbasis of its compressed target.
Article: main_krylov, apA:galerkin(e), trace/nuclear duality.
Proof: cycle the orthogonal factors and cancel their product inside the trace. -/
theorem trace_coordinates {K : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis K)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix.trace (B.coordinates X) = Matrix.trace X := by
  rw [SpectralBasis.coordinates, Matrix.trace_mul_cycle, B.mul_transpose, Matrix.one_mul]

/-- Spectral coordinates take any shifted physical form to the same shifted coordinate form.
Use: compare the diagonal entries of any actual uncertainty matrix with its true norm budget.
Article: main_krylov, apA:galerkin(e), trace support upper bound.
Proof: distribute the congruence and use the genuine orthogonality equation. -/
theorem coordinates_shift {K : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis K)
    (E : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    B.coordinates (ω • 1 + E) = ω • 1 + B.coordinates E := by
  simp only [SpectralBasis.coordinates, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, B.transpose_mul]

/-- The actual sign witness has spectral norm at most one, including a zero target.
Use: scaling it by ω is a genuine admissible spectral perturbation.
Article: main_krylov, apA:galerkin(e), norm of sign(PZP).
Proof: its two shifted forms have nonnegative spectral diagonal entries because
every actual scalar sign belongs to [−1,1]. -/
theorem signInBasis_norm_le {K : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis K) :
    opNorm (signInBasis B) ≤ 1 := by
  have hminus : B.coordinates (1 - signInBasis B) =
      diagonal (fun i => 1 - spectralSign (B.eigenvalues i)) := by
    have h := coordinates_shift B (-signInBasis B) 1
    simp only [one_smul, SpectralBasis.coordinates, Matrix.mul_neg, Matrix.neg_mul,
      ← sub_eq_add_neg] at h
    rw [show B.Qᵀ * signInBasis B * B.Q = diagonal (fun i => spectralSign (B.eigenvalues i))
      from coordinates_sign B] at h
    change B.Qᵀ * (1 - signInBasis B) * B.Q = _
    rw [h]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hplus : B.coordinates (1 + signInBasis B) =
      diagonal (fun i => 1 + spectralSign (B.eigenvalues i)) := by
    rw [show 1 + signInBasis B = (1 : ℝ) • 1 + signInBasis B by rw [one_smul],
      coordinates_shift, one_smul, coordinates_sign]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  apply (spectral_norm_iff_shifted_posSemidef _
    (Matrix.isHermitian_iff_isSymm.mpr (signInBasis_isSymm B)) (by norm_num : (0 : ℝ) ≤ 1)).mpr
  -- The same actual orthogonal basis evaluates both endpoint positivity tests.
  simp only [one_smul]
  constructor
  · rw [← coordinates_posSemidef_iff B (1 - signInBasis B), hminus, posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr ((abs_le.mp (spectralSign_properties _).1).2)
  · rw [← coordinates_posSemidef_iff B (1 + signInBasis B), hplus, posSemidef_diagonal_iff]
    intro i
    linarith [(abs_le.mp (spectralSign_properties (B.eigenvalues i)).1).1]

/-- The actual spectral sign attains the exact finite nuclear pairing with its target.
Use: supplies a concrete norm-feasible maximizing uncertainty matrix.
Article: main_krylov, apA:galerkin(e), tr(sign(K)K)=‖K‖_*.
Proof: preserve the actual trace in the spectral basis, where every summand is sign(λ)λ=|λ|. -/
theorem trace_sign_eq_nuclear (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsHermitian) :
    Matrix.trace (signInBasis (SpectralBasis.ofHermitian K hK) * K) = matrixNuclearNorm K := by
  let B := SpectralBasis.ofHermitian K hK
  have hd : B.coordinates K = diagonal B.eigenvalues := B.diagonalize
  rw [← trace_coordinates B, B.coordinates_mul, coordinates_sign, hd,
    diagonal_mul_diagonal, matrixNuclearNorm_eq K hK]
  simp only [Matrix.trace, Matrix.diag, diagonal_apply_eq]
  exact Finset.sum_congr rfl fun i _ => (spectralSign_properties (B.eigenvalues i)).2

/-- Every actual symmetric spectral perturbation obeys the nuclear trace bound.
Use: the upper half of supported trace/nuclear duality before imposing a subspace support.
Article: main_krylov, apA:galerkin(e), tr(EK)≤ω‖K‖_*.
Proof: transform the true signed norm bounds to the target eigenbasis; each
coordinate diagonal lies in [−ω,ω], giving ω|λ_i| for each trace summand. -/
theorem trace_spectral_bound (E K : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm)
    (hK : K.IsHermitian) {ω : ℝ} (hω : 0 ≤ ω) (hn : opNorm E ≤ ω) :
    Matrix.trace (E * K) ≤ ω * matrixNuclearNorm K := by
  let B := SpectralBasis.ofHermitian K hK
  have hd : B.coordinates K = diagonal B.eigenvalues := B.diagonalize
  have hs := (spectral_norm_iff_shifted_posSemidef E (Matrix.isHermitian_iff_isSymm.mpr hE) hω).mp hn
  have hc : ∀ i, |B.coordinates E i i| ≤ ω := by
    intro i
    have hl := ((coordinates_posSemidef_iff B (ω • 1 + E)).mpr hs.2).diag_nonneg (i := i)
    have hu := ((coordinates_posSemidef_iff B (ω • 1 - E)).mpr hs.1).diag_nonneg (i := i)
    rw [coordinates_shift] at hl
    have hm : B.coordinates (ω • 1 - E) = ω • 1 - B.coordinates E := by
      simpa only [sub_eq_add_neg, SpectralBasis.coordinates, Matrix.mul_neg, Matrix.neg_mul] using
        coordinates_shift B (-E) ω
    rw [hm] at hu
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at hl hu
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- Evaluate the actual trace in K's genuine eigenbasis and bound its summands separately.
  rw [← trace_coordinates B, B.coordinates_mul, hd, matrixNuclearNorm_eq K hK,
    Matrix.trace, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.diag, Matrix.mul_diagonal]
  change B.coordinates E i i * B.eigenvalues i ≤ ω * |B.eigenvalues i|
  calc
    _ ≤ |B.coordinates E i i * B.eigenvalues i| := le_abs_self _
    _ = |B.coordinates E i i| * |B.eigenvalues i| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)

/-- A target supported on the left by P has its actual spectral sign supported by P too.
Use: zero spectral modes stay zero, so a singular compressed target needs no artificial full support.
Article: main_krylov, apA:galerkin(e), support of sign(PZP).
Proof: in the actual spectral coordinates PK=K fixes every nonzero eigenvalue
column; zero eigenvalue columns contribute zero to the sign matrix. -/
theorem sign_left_supported {K : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis K)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPK : P * K = K) : P * signInBasis B = signInBasis B := by
  have hd : B.coordinates K = diagonal B.eigenvalues := B.diagonalize
  have h := congrArg B.coordinates hPK
  rw [B.coordinates_mul, hd] at h
  apply B.coordinates_injective
  rw [B.coordinates_mul, coordinates_sign]
  ext i j
  have he := congrFun (congrFun h i) j
  simp only [Matrix.mul_diagonal] at he ⊢
  -- Only columns with a nonzero actual eigenvalue require cancellation.
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq] at he ⊢
    by_cases hz : B.eigenvalues i = 0
    · simp [spectralSign, hz]
    · have hc : B.coordinates P i i = 1 := mul_right_cancel₀ hz (by simpa only [one_mul] using he)
      rw [hc, one_mul]
  · simp only [diagonal_apply_ne _ hij] at he ⊢
    by_cases hz : B.eigenvalues j = 0
    · simp [spectralSign, hz]
    · have hc : B.coordinates P i j = 0 := (mul_eq_zero.mp he).resolve_right hz
      rw [hc, zero_mul]

/-- A genuinely supported uncertainty matrix pairs with Z exactly as with its compressed target.
Use: both the upper bound and its attaining sign matrix optimize the original trace pairing.
Article: main_krylov, apA:galerkin(e), E=PEP.
Proof: idempotence and actual support give EP=PE=E; cycle the last projector in the trace. -/
theorem trace_supported_target (P E Z : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hE : E = P * E * P) : Matrix.trace (E * (P * Z * P)) = Matrix.trace (E * Z) := by
  have hEP : E * P = E := by
    calc
      _ = (P * E * P) * P := congrArg (fun X => X * P) hE
      _ = P * E * (P * P) := by noncomm_ring
      _ = E := by rw [hP]; exact hE.symm
  have hPE : P * E = E := by
    calc
      _ = P * (P * E * P) := congrArg (fun X => P * X) hE
      _ = (P * P) * E * P := by noncomm_ring
      _ = E := by rw [hP]; exact hE.symm
  -- Both outer projectors are canceled from actual support, not from a range assumption.
  calc
    _ = Matrix.trace (E * P * Z * P) := by congr 1; noncomm_ring
    _ = Matrix.trace (E * Z * P) := by rw [hEP]
    _ = Matrix.trace (P * E * Z) := Matrix.trace_mul_cycle E Z P
    _ = _ := by rw [hPE]

/-- Full attained trace/nuclear duality on an actual orthogonal support, including singular targets.
Use: the final assertion of the window-calculus budget lemma has a concrete supported
maximizing symmetric perturbation and the previously defined actual nuclear norm.
Article: main_krylov, apA:galerkin(e), max_(E=PEP,‖E‖≤ω) tr(EZ)=ω‖PZP‖_*.
Proof: every actual supported perturbation obeys the proved spectral/nuclear trace bound;
the actual spectral sign of PZP is itself supported by P and attains that bound. -/
theorem supported_nuclear_duality (P Z : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm)
    (hPid : P * P = P) (hZ : Z.IsSymm) {ω : ℝ} (hω : 0 ≤ ω) :
    IsGreatest {r : ℝ | ∃ E : Matrix (Fin n) (Fin n) ℝ,
      E.IsSymm ∧ E = P * E * P ∧ opNorm E ≤ ω ∧ r = Matrix.trace (E * Z)}
      (ω * matrixNuclearNorm (P * Z * P)) := by
  let K := P * Z * P
  have hK : K.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    simp only [K, Matrix.IsSymm, transpose_mul, hP.eq, hZ.eq, Matrix.mul_assoc]
  let B := SpectralBasis.ofHermitian K hK
  have hPK : P * K = K := by
    change P * (P * Z * P) = P * Z * P
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPid]
  have hleft := sign_left_supported B P hPK
  have hright : signInBasis B * P = signInBasis B := by
    have h := congrArg Matrix.transpose hleft
    simpa only [transpose_mul, hP.eq, (signInBasis_isSymm B).eq] using h
  let E := ω • signInBasis B
  have hs : E.IsSymm := (signInBasis_isSymm B).smul ω
  have hsupport : E = P * E * P := by
    simp only [E, Matrix.mul_smul, Matrix.smul_mul, hleft, hright]
  have hn : opNorm E ≤ ω := by
    change opNorm (ω • signInBasis B) ≤ ω
    rw [opNorm_smul, abs_of_nonneg hω]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (signInBasis_norm_le B) hω
  constructor
  · refine ⟨E, hs, hsupport, hn, ?_⟩
    rw [← trace_supported_target P E Z hPid hsupport]
    change ω * matrixNuclearNorm K = Matrix.trace ((ω • signInBasis B) * K)
    rw [Matrix.smul_mul, Matrix.trace_smul, trace_sign_eq_nuclear K hK, smul_eq_mul]
  · rintro r ⟨F, hF, hsupportF, hnF, rfl⟩
    -- The upper bound is tested on the same original target Z as the attaining sign scenario.
    rw [← trace_supported_target P F Z hPid hsupportF]
    exact trace_spectral_bound F K hF hK hω hnF

end
end krylov.LinearAlgebra
