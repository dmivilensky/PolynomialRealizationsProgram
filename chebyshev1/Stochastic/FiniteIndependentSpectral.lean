import chebyshev1.Stochastic.IndependentSpectral
import chebyshev1.Stochastic.MatrixMoments

/-! Isotropic iid curvature bounds from the finite samples used by the run,
on their original probability space. No infinite iid extension is required. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {Ω d ι : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d]
  [Fintype ι] [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem finite_independent_weighted_square (z : ℕ → Ω → ℝ) (N : ℕ)
    (hz : iIndepFun (fun s : Fin N => z s.val) μ)
    (hm : ∀ s<N, Measurable (z s)) (hL2 : ∀ s<N, MemLp (z s) 2 μ)
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (a : ℕ → ℝ) :
    (∫ ω, (∑ s∈Finset.range N, a s*z s ω)^2 ∂μ) =
      ∑ s∈Finset.range N, (a s)^2*(∫ ω, (z s ω)^2 ∂μ) := by
  have hh := integral_independent_centered_sum_norm_sq hz
    (fun s => hm s s.isLt) (fun s => (hL2 s s.isLt).integrable (by norm_num))
    (fun s => (hL2 s s.isLt).integrable_sq) (fun s => hmean s s.isLt) (fun s => a s)
  simp only [smul_eq_mul,Real.norm_eq_abs,sq_abs] at hh
  simpa only [← Fin.sum_univ_eq_sum_range,mul_comm] using hh

theorem finite_independent_matrix_isotropic_leading (R : Realization ι) (N : ℕ)
    (eig : d → ℝ) (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun (fun s : Fin N => E s.val) μ)
    (hm : ∀ s<N, Measurable (E s))
    (hL2 : ∀ s<N, ∀ i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s<N, ∀ i j, ∫ ω, E s ω i j ∂μ=0) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N (Matrix.diagonal eig) (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) =
      R.isotropicSpectralEnergy N eig (fun s i j => ∫ ω, (E s ω i j)^2 ∂μ) := by
  simp_rw [uniformSphere_matrix_norm_sq]
  rw [integral_div]
  unfold Realization.isotropicSpectralEnergy hsSq
  congr 1
  have hint (i j : d) : Integrable (fun ω =>
      (R.linearResponse N (Matrix.diagonal eig) (fun s => E s ω) i j)^2) μ := by
    have hh : MemLp (fun ω => ∑ s∈Finset.range N,
        R.kernel N s (eig i) (eig j)*E s ω i j) 2 μ :=
      memLp_finsetSum _ (fun s hs => (hL2 s (Finset.mem_range.mp hs) i j).const_mul _)
    simpa only [R.diagonal_linearResponse_entry] using hh.integrable_sq
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j _
  have hind := hE.comp (fun _ M => M i j) (fun _ => Matrix.measurable_apply)
  simp_rw [R.diagonal_linearResponse_entry]
  exact finite_independent_weighted_square (fun s ω => E s ω i j) N hind
    (fun s hs => (hm s hs).eval_matrix) (fun s hs => hL2 s hs i j)
    (fun s hs => hmean s hs i j) (fun s => R.kernel N s (eig i) (eig j))

theorem finite_independent_matrix_isotropic_spectral (R : Realization ι) (N : ℕ)
    {H : Matrix d d ℝ} (B : SpectralBasis H) (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun (fun s : Fin N => E s.val) μ)
    (hm : ∀ s<N, Measurable (E s))
    (hL2 : ∀ s<N, ∀ i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s<N, ∀ i j, ∫ ω, E s ω i j ∂μ=0) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N H (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) =
      R.isotropicSpectralEnergy N B.eigenvalues
        (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ) := by
  have hc := finite_independent_matrix_isotropic_leading R N B.eigenvalues
    (fun s ω => B.coordinates (E s ω)) (hE.comp (fun _ => B.coordinates)
      (fun _ => B.coordinates_continuous.measurable))
    (fun s hs => B.coordinates_continuous.measurable.comp (hm s hs))
    (fun s hs => B.coordinates_memLp (hL2 s hs))
    (fun s hs => B.coordinates_mean_zero (hL2 s hs) (hmean s hs))
  have hhs (ω) : hsSq (R.linearResponse N (Matrix.diagonal B.eigenvalues)
      (fun s => B.coordinates (E s ω))) = hsSq (R.linearResponse N H (fun s => E s ω)) := by
    have hh := R.linearResponse_coordinates B.Q H B.transpose_mul B.mul_transpose N
      (fun s => E s ω)
    rw [B.diagonalize] at hh
    change R.linearResponse N (Matrix.diagonal B.eigenvalues)
      (fun s => B.coordinates (E s ω)) = B.coordinates (R.linearResponse N H (fun s => E s ω)) at hh
    rw [hh]
    exact B.coordinates_hsSq _
  simp_rw [uniformSphere_matrix_norm_sq,hhs] at hc
  simpa only [uniformSphere_matrix_norm_sq] using hc

omit [DecidableEq d] in
private theorem spectralEnergy_congr_upto (R : Realization ι) (N : ℕ) (eig : d → ℝ)
    (C D : ℕ → d → d → ℝ) (he : ∀ s<N, ∀ i j, C s i j=D s i j) :
    R.isotropicSpectralEnergy N eig C=R.isotropicSpectralEnergy N eig D := by
  unfold Realization.isotropicSpectralEnergy
  apply congrArg (fun x : ℝ => x/(Fintype.card d:ℝ))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s hs
  rw [he s (Finset.mem_range.mp hs)]

theorem finite_independent_matrix_isotropic_iid_bound (R : Realization ι) (I : SpectralInterval)
    {N : ℕ} (hN : 0<N) {H : Matrix d d ℝ} (B : SpectralBasis H)
    (heig : ∀ i, B.eigenvalues i∈Set.Icc I.mu I.L)
    (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun (fun s : Fin N => E s.val) μ)
    (hm : ∀ s<N, Measurable (E s))
    (hL2 : ∀ s<N, ∀ i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s<N, ∀ i j, ∫ ω, E s ω i j ∂μ=0)
    (hiid : ∀ s<N, IdentDistrib (E s) (E 0) μ μ) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N H (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) ≤
      R.gain I N^2/(Fintype.card d:ℝ)*(∫ ω, hsSq (E 0 ω) ∂μ) := by
  rw [finite_independent_matrix_isotropic_spectral R N B E hE hm hL2 hmean]
  have hcov (s : ℕ) (hs : s<N) (i j : d) :
      (∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ) =
        ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ := by
    simpa only [Function.comp_apply] using ((hiid s hs).comp
      (B.coordinates_continuous.measurable.eval_matrix.pow_const 2)).integral_eq
  rw [spectralEnergy_congr_upto R N B.eigenvalues
    (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ)
    (fun _ i j => ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ)
    hcov]
  have hb := R.isotropicSpectralEnergy_iid_bound I N B.eigenvalues heig
    (fun i j => ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ)
    (fun i j => integral_nonneg (fun _ => sq_nonneg _))
  rw [independent_matrix_coupling_mass B (E 0) (hL2 0 hN)] at hb
  exact hb.trans_eq (by ring)

theorem finite_independent_matrix_isotropic_iid_attained (R : Realization ι) (I : SpectralInterval)
    {N : ℕ} (hN : 0<N) {H : Matrix d d ℝ} (B : SpectralBasis H)
    (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun (fun s : Fin N => E s.val) μ)
    (hm : ∀ s<N, Measurable (E s))
    (hL2 : ∀ s<N, ∀ i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s<N, ∀ i j, ∫ ω, E s ω i j ∂μ=0)
    (hiid : ∀ s<N, IdentDistrib (E s) (E 0) μ μ)
    (p q : d) (hmax : R.kernelNorm N (B.eigenvalues p) (B.eigenvalues q)=R.gain I N)
    (hsupport : ∀ i j, (i≠p ∨ j≠q) → ∀ᵐ ω∂μ, B.coordinates (E 0 ω) i j=0) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N H (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) =
      R.gain I N^2/(Fintype.card d:ℝ)*(∫ ω, hsSq (E 0 ω) ∂μ) := by
  rw [finite_independent_matrix_isotropic_spectral R N B E hE hm hL2 hmean]
  have hcov (s : ℕ) (hs : s<N) (i j : d) :
      (∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ) =
        ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ := by
    simpa only [Function.comp_apply] using ((hiid s hs).comp
      (B.coordinates_continuous.measurable.eval_matrix.pow_const 2)).integral_eq
  rw [spectralEnergy_congr_upto R N B.eigenvalues
    (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ)
    (fun _ i j => ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ)
    hcov]
  have hc (i j : d) (hh : (∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ)≠0) :
      R.kernelNorm N (B.eigenvalues i) (B.eigenvalues j)=R.gain I N := by
    by_cases hip : i=p
    · by_cases hjq : j=q
      · simpa only [hip,hjq] using hmax
      · exfalso
        apply hh
        calc
          _ = ∫ _ : Ω, (0:ℝ) ∂μ := integral_congr_ae
            ((hsupport i j (Or.inr hjq)).mono (fun _ h => by rw [h]; norm_num))
          _ = 0 := integral_zero _ _
    · exfalso
      apply hh
      calc
        _ = ∫ _ : Ω, (0:ℝ) ∂μ := integral_congr_ae
          ((hsupport i j (Or.inl hip)).mono (fun _ h => by rw [h]; norm_num))
        _ = 0 := integral_zero _ _
  rw [R.isotropicSpectralEnergy_iid_eq I N B.eigenvalues _ hc,
    independent_matrix_coupling_mass B (E 0) (hL2 0 hN)]
  ring

omit [IsProbabilityMeasure μ] in
/-- The iid spectral coefficient itself has the gain bound. This form applies
directly to the coefficient in the actual-run variance expansion. -/
theorem finite_iid_spectralEnergy_bound (R : Realization ι) (I : SpectralInterval)
    (N : ℕ) {H : Matrix d d ℝ} (B : SpectralBasis H)
    (heig : ∀ i, B.eigenvalues i∈Set.Icc I.mu I.L) (E : ℕ → Ω → Matrix d d ℝ)
    (hL2 : ∀ i j, MemLp (fun ω => E 0 ω i j) 2 μ)
    (hiid : ∀ s<N, IdentDistrib (E s) (E 0) μ μ) :
    R.isotropicSpectralEnergy N B.eigenvalues
      (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ) ≤
        R.gain I N^2/(Fintype.card d:ℝ)*(∫ ω, hsSq (E 0 ω) ∂μ) := by
  have he := spectralEnergy_congr_upto R N B.eigenvalues
    (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ)
    (fun _ i j => ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ) (fun s hs i j => by
      simpa only [Function.comp_apply] using ((hiid s hs).comp
        (B.coordinates_continuous.measurable.eval_matrix.pow_const 2)).integral_eq)
  rw [he]
  have hb := R.isotropicSpectralEnergy_iid_bound I N B.eigenvalues heig
    (fun i j => ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ)
    (fun i j => integral_nonneg (fun _ => sq_nonneg _))
  rw [independent_matrix_coupling_mass B (E 0) hL2] at hb
  exact hb.trans_eq (by ring)

omit [IsProbabilityMeasure μ] in
/-- Arbitrary covariance support on maximizing spectral pairs attains equality;
entire repeated-eigenvalue blocks are permitted. -/
theorem finite_iid_spectralEnergy_attained (R : Realization ι) (I : SpectralInterval)
    (N : ℕ) {H : Matrix d d ℝ} (B : SpectralBasis H) (E : ℕ → Ω → Matrix d d ℝ)
    (hL2 : ∀ i j, MemLp (fun ω => E 0 ω i j) 2 μ)
    (hiid : ∀ s<N, IdentDistrib (E s) (E 0) μ μ)
    (hmax : ∀ i j, (∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ)≠0 →
      R.kernelNorm N (B.eigenvalues i) (B.eigenvalues j)=R.gain I N) :
    R.isotropicSpectralEnergy N B.eigenvalues
      (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ) =
        R.gain I N^2/(Fintype.card d:ℝ)*(∫ ω, hsSq (E 0 ω) ∂μ) := by
  have he := spectralEnergy_congr_upto R N B.eigenvalues
    (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ)
    (fun _ i j => ∫ ω, (B.coordinates (E 0 ω) i j)^2 ∂μ) (fun s hs i j => by
      simpa only [Function.comp_apply] using ((hiid s hs).comp
        (B.coordinates_continuous.measurable.eval_matrix.pow_const 2)).integral_eq)
  rw [he,R.isotropicSpectralEnergy_iid_eq I N B.eigenvalues _ hmax,
    independent_matrix_coupling_mass B (E 0) hL2]
  ring

omit [IsProbabilityMeasure μ] in
/-- Noise supported on a maximizing pair of eigenspaces attains the iid bound.
The eigenspaces may have arbitrary multiplicity, and all entries within their
rectangular coupling block may be correlated. -/
theorem finite_iid_eigenspace_energy_attained (R : Realization ι) (I : SpectralInterval)
    (N : ℕ) {H : Matrix d d ℝ} (B : SpectralBasis H) (E : ℕ → Ω → Matrix d d ℝ)
    (hL2 : ∀ i j, MemLp (fun ω => E 0 ω i j) 2 μ)
    (hiid : ∀ s<N, IdentDistrib (E s) (E 0) μ μ)
    (lam nu : ℝ) (hmax : R.kernelNorm N lam nu=R.gain I N)
    (hsupport : ∀ i j, (B.eigenvalues i≠lam ∨ B.eigenvalues j≠nu) →
      ∀ᵐ ω ∂μ, B.coordinates (E 0 ω) i j=0) :
    R.isotropicSpectralEnergy N B.eigenvalues
      (fun s i j => ∫ ω, (B.coordinates (E s ω) i j)^2 ∂μ) =
        R.gain I N^2/(Fintype.card d:ℝ)*(∫ ω, hsSq (E 0 ω) ∂μ) := by
  apply finite_iid_spectralEnergy_attained R I N B E hL2 hiid
  intro i j hij
  by_cases hi : B.eigenvalues i=lam
  · by_cases hj : B.eigenvalues j=nu
    · simpa only [hi,hj] using hmax
    · exfalso
      apply hij
      calc
        _ = ∫ _ : Ω, (0:ℝ) ∂μ := integral_congr_ae
          ((hsupport i j (Or.inr hj)).mono (fun _ h => by rw [h]; norm_num))
        _ = 0 := integral_zero _ _
  · exfalso
    apply hij
    calc
      _ = ∫ _ : Ω, (0:ℝ) ∂μ := integral_congr_ae
        ((hsupport i j (Or.inl hi)).mono (fun _ h => by rw [h]; norm_num))
      _ = 0 := integral_zero _ _

theorem finite_independent_matrix_iid_eigenspace_attained (R : Realization ι)
    (I : SpectralInterval) {N : ℕ} (hN : 0<N) {H : Matrix d d ℝ} (B : SpectralBasis H)
    (E : ℕ → Ω → Matrix d d ℝ) [Nonempty d]
    (hE : iIndepFun (fun s : Fin N => E s.val) μ) (hm : ∀ s<N, Measurable (E s))
    (hL2 : ∀ s<N, ∀ i j, MemLp (fun ω => E s ω i j) 2 μ)
    (hmean : ∀ s<N, ∀ i j, ∫ ω, E s ω i j ∂μ=0)
    (hiid : ∀ s<N, IdentDistrib (E s) (E 0) μ μ)
    (lam nu : ℝ) (hmax : R.kernelNorm N lam nu=R.gain I N)
    (hsupport : ∀ i j, (B.eigenvalues i≠lam ∨ B.eigenvalues j≠nu) →
      ∀ᵐ ω ∂μ, B.coordinates (E 0 ω) i j=0) :
    (∫ ω, ∫ x : Metric.sphere (0:EuclideanSpace ℝ d) 1,
      ‖WithLp.toLp 2 ((R.linearResponse N H (fun s => E s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂uniformSphere (EuclideanSpace ℝ d) ∂μ) =
      R.gain I N^2/(Fintype.card d:ℝ)*(∫ ω, hsSq (E 0 ω) ∂μ) := by
  rw [finite_independent_matrix_isotropic_spectral R N B E hE hm hL2 hmean]
  exact finite_iid_eigenspace_energy_attained R I N B E (hL2 0 hN) hiid lam nu hmax hsupport

end
end chebyshev1.Stochastic
