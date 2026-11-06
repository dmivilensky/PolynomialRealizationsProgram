import chebyshev1.Stochastic.IndependentSpectral
import chebyshev1.Stochastic.ImpulseMatrix
import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini bridges for a genuine independent uniform initial direction. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {Ω d : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d] [Nonempty d]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
local notation "V" => EuclideanSpace ℝ d
local notation "Sph" => Metric.sphere (0:V) 1

omit [Nonempty d] [IsProbabilityMeasure μ] [DecidableEq d] in
theorem matrix_sandwich_memLp (A B : Matrix d d ℝ) (M : Ω → Matrix d d ℝ)
    (hL2 : ∀ i j, MemLp (fun ω => M ω i j) 2 μ) (i j : d) :
    MemLp (fun ω => (A*M ω*B) i j) 2 μ := by
  simp only [Matrix.mul_apply]
  apply memLp_finsetSum
  intro k _
  exact (memLp_finsetSum _ (fun l _ => (hL2 l k).const_mul (A i l))).mul_const (B k j)

omit [Nonempty d] [IsProbabilityMeasure μ] in
theorem curvatureImpulse_memLp (S : TwoTerm) (H : Matrix d d ℝ) (N s : ℕ)
    (M : Ω → Matrix d d ℝ) (hL2 : ∀ i j, MemLp (fun ω => M ω i j) 2 μ) (i j : d) :
    MemLp (fun ω => S.curvatureImpulse H N s (M ω) i j) 2 μ := by
  simpa only [TwoTerm.curvatureImpulse, Matrix.smul_apply, smul_eq_mul] using
    (matrix_sandwich_memLp
      (orderedProduct (fun i => S.memoryStep (s+1+i) H) (N-(s+1)) 0 0)
      (S.realization.operatorTransfer s (fun _ => H)) M hL2 i j).const_mul (-S.gamma s)

omit [Nonempty d] [IsProbabilityMeasure μ] in
theorem curvatureImpulse_measurable (S : TwoTerm) (H : Matrix d d ℝ) (N s : ℕ)
    (M : Ω → Matrix d d ℝ) (hm : Measurable M) :
    Measurable (fun ω => S.curvatureImpulse H N s (M ω)) := by
  unfold TwoTerm.curvatureImpulse
  fun_prop

omit [IsProbabilityMeasure μ] in
theorem sphere_random_matrix_integrable (M : Ω → Matrix d d ℝ) (hm : Measurable M)
    (hL2 : ∀ i j, MemLp (fun ω => M ω i j) 2 μ) :
    Integrable (fun p : Ω × Sph =>
      ‖WithLp.toLp 2 ((M p.1).mulVec (WithLp.ofLp p.2.val))‖^2)
      (μ.prod (uniformSphere V)) := by
  have hme : Measurable (fun p : Ω × Sph =>
      ‖WithLp.toLp 2 ((M p.1).mulVec (WithLp.ofLp p.2.val))‖^2) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.measurable_sum
    intro i _
    apply Measurable.pow_const
    change Measurable (fun p : Ω × Sph => ∑ j, M p.1 i j*p.2.val j)
    apply Finset.measurable_sum
    intro j _
    have hx : Continuous (fun x : Sph => x.val j) := by fun_prop
    exact ((hm.eval_matrix).comp measurable_fst).mul (hx.measurable.comp measurable_snd)
  apply (integrable_prod_iff hme.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun ω => by
      have hc : Continuous (fun x : Sph =>
        ‖WithLp.toLp 2 ((M ω).mulVec (WithLp.ofLp x.val))‖^2) := by fun_prop
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  · have hi : Integrable (fun ω => hsSq (M ω)) μ := by
      exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => (hL2 i j).integrable_sq))
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm, uniformSphere_matrix_norm_sq]
      using hi.div_const (Fintype.card d:ℝ)

theorem sphere_random_matrix_average (M : Ω → Matrix d d ℝ) (hm : Measurable M)
    (hL2 : ∀ i j, MemLp (fun ω => M ω i j) 2 μ) :
    (∫ x : Sph, ∫ ω,
      ‖WithLp.toLp 2 ((M ω).mulVec (WithLp.ofLp x.val))‖^2 ∂μ ∂uniformSphere V) =
        (∫ ω, hsSq (M ω) ∂μ)/(Fintype.card d:ℝ) := by
  rw [← integral_integral_swap (sphere_random_matrix_integrable M hm hL2)]
  simp_rw [uniformSphere_matrix_norm_sq]
  exact integral_div _ _

omit [Nonempty d] [IsProbabilityMeasure μ] in
theorem expected_curvatureImpulse_hsSq_spectral (S : TwoTerm) {N s : ℕ} (hs : s<N)
    {H : Matrix d d ℝ} (B : SpectralBasis H) (M : Ω → Matrix d d ℝ)
    (hL2 : ∀ i j, MemLp (fun ω => M ω i j) 2 μ) :
    (∫ ω, hsSq (S.curvatureImpulse H N s (M ω)) ∂μ) =
      ∑ i, ∑ j, S.realization.kernel N s (B.eigenvalues i) (B.eigenvalues j)^2 *
        (∫ ω, (B.coordinates (M ω) i j)^2 ∂μ) := by
  have he (ω : Ω) : hsSq (S.curvatureImpulse H N s (M ω)) =
      ∑ i, ∑ j, S.realization.kernel N s (B.eigenvalues i) (B.eigenvalues j)^2 *
        (B.coordinates (M ω) i j)^2 := by
    rw [← B.coordinates_hsSq, S.curvatureImpulse_coordinates hs]
    unfold hsSq
    simp_rw [S.curvatureImpulse_diagonal_entry hs, mul_pow]
  simp_rw [he]
  have hi (i j : d) := ((B.coordinates_memLp hL2 i j).integrable_sq).const_mul
    (S.realization.kernel N s (B.eigenvalues i) (B.eigenvalues j)^2)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul]

/-- Averaging the actual independent-noise leading coefficient over initial
directions gives the spectral sum, with no unproved exchange of integrals. -/
theorem sphere_curvature_impulse_energy_spectral (S : TwoTerm) (N : ℕ)
    {H : Matrix d d ℝ} (B : SpectralBasis H) (M : ℕ → Ω → Matrix d d ℝ)
    (hm : ∀ s, Measurable (M s)) (hL2 : ∀ s i j, MemLp (fun ω => M s ω i j) 2 μ) :
    (∫ x : Sph, ∑ s ∈ Finset.range N, ∫ ω,
      ‖WithLp.toLp 2 ((S.curvatureImpulse H N s (M s ω)).mulVec
        (WithLp.ofLp x.val))‖^2 ∂μ ∂uniformSphere V) =
      S.realization.isotropicSpectralEnergy N B.eigenvalues
        (fun s i j => ∫ ω, (B.coordinates (M s ω) i j)^2 ∂μ) := by
  have hi (s : ℕ) := (sphere_random_matrix_integrable
    (fun ω => S.curvatureImpulse H N s (M s ω))
    (curvatureImpulse_measurable S H N s (M s) (hm s))
    (curvatureImpulse_memLp S H N s (M s) (hL2 s))).integral_prod_right
  rw [integral_finsetSum _ (fun s _ => hi s)]
  simp_rw [sphere_random_matrix_average _ (curvatureImpulse_measurable S H N _ _ (hm _))
    (curvatureImpulse_memLp S H N _ _ (hL2 _))]
  rw [← Finset.sum_div]
  unfold Realization.isotropicSpectralEnergy
  apply congrArg (fun x : ℝ => x/(Fintype.card d:ℝ))
  calc
    _ = ∑ s ∈ Finset.range N, ∑ i, ∑ j,
        S.realization.kernel N s (B.eigenvalues i) (B.eigenvalues j)^2 *
          (∫ ω, (B.coordinates (M s ω) i j)^2 ∂μ) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact expected_curvatureImpulse_hsSq_spectral S (Finset.mem_range.mp hs) B (M s) (hL2 s)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

end
end chebyshev1.Stochastic
