import krylov.Strings.SpectralScalar
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
Article: main_krylov, thm:value, spectral atom from the true constant mode.
Use: identify the atom at 1 of the actual scalar spectral measure of a
selfadjoint contraction with the genuine orthogonal fixed-space projection.
After the Neumann resolvent's spectral change this is the atom at zero.
Source: von Neumann's mean ergodic theorem and scalar dominated convergence.
-/

namespace krylov.Strings.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported ContinuousFunctionalCalculus

/-- Scalar Cesàro averages of geometric powers. -/
def cesaroValue (n : ℕ) (r : ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, r ^ i

/-- Geometric Cesàro averages are uniformly bounded on [-1,1]. -/
theorem abs_cesaroValue_le_one {r : ℝ} (hr : |r| ≤ 1) (n : ℕ) : |cesaroValue n r| ≤ 1 := by
  by_cases hn : n = 0
  · simp [cesaroValue, hn]
  have hnp : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  calc
    _ = (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, r ^ i| := by
      rw [cesaroValue, abs_mul, abs_inv, abs_of_pos hnp]
    _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |r ^ i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hnp.le)
    _ ≤ (n : ℝ)⁻¹ * n := by
      gcongr
      calc
        (∑ i ∈ Finset.range n, |r ^ i|) ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_pow]
          exact pow_le_one₀ (abs_nonneg r) hr
        _ = n := by simp
    _ = 1 := inv_mul_cancel₀ hnp.ne'

/-- Scalar Cesàro averages converge exactly to the indicator of r=1,
including the endpoint r=-1. -/
theorem cesaroValue_tendsto {r : ℝ} (hr : |r| ≤ 1) :
    Tendsto (fun n => cesaroValue n r) atTop (𝓝 (if r = 1 then 1 else 0)) := by
  by_cases he : r = 1
  · subst r
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [cesaroValue, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℝ) ≠ 0)]
  · rw [ite_eq_right he]
    have hmul : ∀ n, (r - 1) * cesaroValue n r = (n : ℝ)⁻¹ * (r ^ n - 1) := by
      intro n
      dsimp [cesaroValue]
      calc
        _ = (n : ℝ)⁻¹ * ((r - 1) * ∑ i ∈ Finset.range n, r ^ i) := by ring
        _ = _ := by rw [mul_geom_sum]
    have hlim : Tendsto (fun n => (r - 1) * cesaroValue n r) atTop (𝓝 0) := by
      apply squeeze_zero_norm _ (show Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * 2) atTop (𝓝 0) from by
        have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        simpa only [zero_mul] using hi.mul_const 2)
      intro n
      rw [hmul n, norm_mul, Real.norm_eq_abs ((n : ℝ)⁻¹), abs_inv, abs_of_nonneg (Nat.cast_nonneg n)]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg n))
      calc
        ‖r ^ n - 1‖ ≤ ‖r ^ n‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ ≤ 2 := by
          rw [norm_pow, Real.norm_eq_abs r, norm_one]
          linarith [pow_le_one₀ (abs_nonneg r) hr (n := n)]
    have h := hlim.div_const (r - 1)
    simpa only [mul_div_cancel_left₀ _ (sub_ne_zero.2 he), zero_div] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The actual real linear scalar pairing with one fixed vector. -/
def vectorFunctional (v : E) : E →L[ℝ] ℝ :=
  Complex.reCLM.comp ((innerSL ℂ v).restrictScalars ℝ)

/-- All moments of the constructed scalar measure are actual operator powers. -/
theorem scalarMeasure_moment (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) (k : ℕ) :
    (∫ x, (x : ℝ) ^ k ∂scalarMeasure T hT v) = vectorFunctional v ((T ^ k) v) := by
  change (∫ x, (x : ℝ) ^ k ∂scalarMeasure T hT v) = (inner ℂ v ((T ^ k) v)).re
  have he := scalarMeasure_integral T hT v (((ContinuousMap.id ℝ).restrict (spectrum ℝ T)) ^ k)
  simpa only [ContinuousMap.pow_apply, ContinuousMap.restrict_apply, ContinuousMap.id_apply,
    scalarCFC, map_pow, cfcHom_id] using he

/-- The exact Cesàro spectral integral is the actual operator orbit average. -/
theorem scalarMeasure_cesaro_integral (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) (n : ℕ) :
    (∫ x, cesaroValue n (x : ℝ) ∂scalarMeasure T hT v) =
      vectorFunctional v (birkhoffAverage ℂ T id n v) := by
  have hi : ∀ k, Integrable (fun x : spectrum ℝ T => (x : ℝ) ^ k) (scalarMeasure T hT v) := by
    intro k
    have hc : Continuous (fun x : spectrum ℝ T => (x : ℝ) ^ k) := continuous_subtype_val.pow k
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ := scalarMeasure T hT v) isCompact_univ
  simp only [cesaroValue, integral_const_mul, integral_finsetSum _ (fun k _ => hi k), scalarMeasure_moment]
  have horbit : (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (T ^ k) v) = birkhoffAverage ℂ T id n v := by
    rw [← birkhoffAverage_apply_congr_ring ℝ ℂ]
    simp only [birkhoffAverage, birkhoffSum, id_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact congrFun (FunLike.coe_pow_eq_iterate T k) v
  rw [← horbit, map_smul, map_sum, smul_eq_mul]

/-- The atom at the fixed eigenvalue of a selfadjoint contraction equals the
genuine squared orthogonal projection of the scalar vector to its fixed space.
The measure itself was constructed by CFC/Riesz–Markov. -/
theorem scalarMeasure_real_fixed_atom [Nontrivial E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (hcontract : ‖T‖ ≤ 1) (v : E) :
    (scalarMeasure T hT v).real {x | (x : ℝ) = 1} =
      ‖(T.eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v‖ ^ 2 := by
  have hsp : ∀ x : spectrum ℝ T, |(x : ℝ)| ≤ 1 := fun x =>
    (show |(x : ℝ)| ≤ ‖T‖ from by simpa only [Real.norm_eq_abs] using
      spectrum.norm_le_norm_of_mem x.property).trans hcontract
  have hlim := tendsto_integral_of_dominated_convergence (μ := scalarMeasure T hT v)
    (F := fun n x => cesaroValue n (x : ℝ)) (f := fun x => if (x : ℝ) = 1 then 1 else 0)
    (fun _ => (1 : ℝ))
    (fun n => (show Continuous (fun x : spectrum ℝ T => cesaroValue n (x : ℝ)) from by
      unfold cesaroValue
      fun_prop).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using abs_cesaroValue_le_one (hsp x) n))
    (Eventually.of_forall (fun x => cesaroValue_tendsto (hsp x)))
  have hint : (∫ x : spectrum ℝ T, (if (x : ℝ) = 1 then (1 : ℝ) else 0) ∂scalarMeasure T hT v) =
      (scalarMeasure T hT v).real {x | (x : ℝ) = 1} := by
    change (∫ x, ({x : spectrum ℝ T | (x : ℝ) = 1}).indicator (fun _ => (1 : ℝ)) x
      ∂scalarMeasure T hT v) = _
    simp only [integral_indicator_const (1 : ℝ) (isClosed_eq continuous_subtype_val continuous_const).measurableSet,
      smul_eq_mul, mul_one]
  rw [hint] at hlim
  simp only [scalarMeasure_cesaro_integral] at hlim
  have hME := (vectorFunctional v).continuous.tendsto
    ((T.eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v : E) |>.comp
      (T.tendsto_birkhoffAverage_orthogonalProjection hcontract v)
  have hproj : vectorFunctional v
      ((T.eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v) =
        ‖(T.eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v‖ ^ 2 := by
    change RCLike.re (inner ℂ v ((T.eqLocus (1 : E →L[ℂ] E)).starProjection v)) = _
    rw [inner_re_symm]
    exact Submodule.re_inner_starProjection_eq_normSq _ _
  rw [hproj] at hME
  exact tendsto_nhds_unique hlim hME

/-- Extended-measure form of the true fixed-eigenvalue atom formula. -/
theorem scalarMeasure_fixed_atom [Nontrivial E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (hcontract : ‖T‖ ≤ 1) (v : E) :
    scalarMeasure T hT v {x | (x : ℝ) = 1} = ENNReal.ofReal
      (‖(T.eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v‖ ^ 2) := by
  rw [← scalarMeasure_real_fixed_atom T hT hcontract v]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- Continuous functions of the operator have genuine scalar spectral
moments under the already constructed measure of the original operator. -/
theorem scalarMeasure_cfc_moment (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (g : C(spectrum ℝ T, ℝ)) (k : ℕ) :
    (∫ x, g x ^ k ∂scalarMeasure T hT v) = vectorFunctional v (((cfcHom hT g) ^ k) v) := by
  change (∫ x, g x ^ k ∂scalarMeasure T hT v) = (inner ℂ v (((cfcHom hT g) ^ k) v)).re
  simpa only [ContinuousMap.pow_apply, scalarCFC, map_pow] using scalarMeasure_integral T hT v (g ^ k)

/-- Cesàro integrals for a continuous spectral function are the actual
Hilbert-space orbit averages of that continuous function of the operator. -/
theorem scalarMeasure_cfc_cesaro_integral (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (g : C(spectrum ℝ T, ℝ)) (n : ℕ) :
    (∫ x, cesaroValue n (g x) ∂scalarMeasure T hT v) =
      vectorFunctional v (birkhoffAverage ℂ (cfcHom hT g) id n v) := by
  have hi : ∀ k, Integrable (fun x => g x ^ k) (scalarMeasure T hT v) := by
    intro k
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (show Continuous (fun x => g x ^ k) from g.continuous.pow k).continuousOn.integrableOn_compact
        (μ := scalarMeasure T hT v) isCompact_univ
  simp only [cesaroValue, integral_const_mul, integral_finsetSum _ (fun k _ => hi k), scalarMeasure_cfc_moment]
  have horbit : (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, ((cfcHom hT g) ^ k) v) =
      birkhoffAverage ℂ (cfcHom hT g) id n v := by
    rw [← birkhoffAverage_apply_congr_ring ℝ ℂ]
    simp only [birkhoffAverage, birkhoffSum, id_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact congrFun (FunLike.coe_pow_eq_iterate (cfcHom hT g) k) v
  rw [← horbit, map_smul, map_sum, smul_eq_mul]

/-- Fixed-mode atom formula after a genuine continuous spectral change. -/
theorem scalarMeasure_real_cfc_fixed_atom [Nontrivial E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (v : E) (g : C(spectrum ℝ T, ℝ)) (hcontract : ‖cfcHom hT g‖ ≤ 1) :
    (scalarMeasure T hT v).real {x | g x = 1} =
      ‖((cfcHom hT g).eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v‖ ^ 2 := by
  have hsp : ∀ x, |g x| ≤ 1 := by
    intro x
    have hs : g x ∈ spectrum ℝ (cfcHom hT g) := by
      rw [cfcHom_map_spectrum]
      exact mem_range_self x
    have hn : |g x| ≤ ‖cfcHom hT g‖ := by
      simpa only [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hs)
    exact hn.trans hcontract
  have hlim := tendsto_integral_of_dominated_convergence (μ := scalarMeasure T hT v)
    (F := fun n x => cesaroValue n (g x)) (f := fun x => if g x = 1 then 1 else 0)
    (fun _ => (1 : ℝ))
    (fun n => (show Continuous (fun x => cesaroValue n (g x)) from by
      unfold cesaroValue
      fun_prop).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using abs_cesaroValue_le_one (hsp x) n))
    (Eventually.of_forall (fun x => cesaroValue_tendsto (hsp x)))
  have hint : (∫ x, (if g x = 1 then (1 : ℝ) else 0) ∂scalarMeasure T hT v) =
      (scalarMeasure T hT v).real {x | g x = 1} := by
    change (∫ x, ({x | g x = 1}).indicator (fun _ => (1 : ℝ)) x ∂scalarMeasure T hT v) = _
    simp only [integral_indicator_const (1 : ℝ) (isClosed_eq g.continuous continuous_const).measurableSet,
      smul_eq_mul, mul_one]
  rw [hint] at hlim
  simp only [scalarMeasure_cfc_cesaro_integral] at hlim
  have hME := (vectorFunctional v).continuous.tendsto
    (((cfcHom hT g).eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v : E) |>.comp
      ((cfcHom hT g).tendsto_birkhoffAverage_orthogonalProjection hcontract v)
  have hproj : vectorFunctional v
      (((cfcHom hT g).eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v) =
        ‖((cfcHom hT g).eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v‖ ^ 2 := by
    change RCLike.re (inner ℂ v (((cfcHom hT g).eqLocus (1 : E →L[ℂ] E)).starProjection v)) = _
    rw [inner_re_symm]
    exact Submodule.re_inner_starProjection_eq_normSq _ _
  rw [hproj] at hME
  exact tendsto_nhds_unique hlim hME

/-- The true zero eigenatom is the squared projection onto the actual kernel.
For a Neumann resolvent, the complementary contraction bound follows from
compression of the complementary energy-graph projection. -/
theorem scalarMeasure_zero_atom [Nontrivial E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (hcomplement : ‖1 - T‖ ≤ 1) (v : E) :
    scalarMeasure T hT v {x | (x : ℝ) = 0} = ENNReal.ofReal (‖T.ker.orthogonalProjectionOnto v‖ ^ 2) := by
  let g : C(spectrum ℝ T, ℝ) := 1 - (ContinuousMap.id ℝ).restrict (spectrum ℝ T)
  have hS : cfcHom hT g = 1 - T := by simp only [g, map_sub, map_one, cfcHom_id]
  have hfix : (1 - T).eqLocus (1 : E →L[ℂ] E) = T.ker := by
    ext x
    change x - T x = x ↔ T x = 0
    exact sub_eq_self
  have he := scalarMeasure_real_cfc_fixed_atom T hT v g (by simpa only [hS] using hcomplement)
  have hset : {x | g x = 1} = {x : spectrum ℝ T | (x : ℝ) = 0} := by
    ext x
    change 1 - (x : ℝ) = 1 ↔ (x : ℝ) = 0
    exact sub_eq_self
  rw [hset, hS] at he
  have hnorm : ‖((1 - T).eqLocus (1 : E →L[ℂ] E)).orthogonalProjectionOnto v‖ =
      ‖T.ker.orthogonalProjectionOnto v‖ := by
    have hcongr : ∀ (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection],
        K = L → ‖K.orthogonalProjectionOnto v‖ = ‖L.orthogonalProjectionOnto v‖ := by
      intro K L _ _ h
      subst L
      rfl
    exact hcongr _ _ hfix
  rw [hnorm] at he
  rw [← he]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

end
end krylov.Strings.Spectral
