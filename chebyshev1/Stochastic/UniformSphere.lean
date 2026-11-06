import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import chebyshev1.Spectral.HilbertSchmidt

/-! The normalized spherical Haar measure and its exact second moments. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators Pointwise RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A linear isometry acts on the unit sphere. -/
def sphereMap (f : E ≃ₗᵢ[ℝ] E) (x : sphere (0:E) 1) : sphere (0:E) 1 :=
  ⟨f x, by simpa only [mem_sphere_zero_iff_norm, f.norm_map] using x.property⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphereMap_continuous (f : E ≃ₗᵢ[ℝ] E) : Continuous (sphereMap f) :=
  (f.continuous.comp continuous_subtype_val).subtype_mk _

def sphereHomeomorph (f : E ≃ₗᵢ[ℝ] E) : sphere (0:E) 1 ≃ₜ sphere (0:E) 1 where
  toFun := sphereMap f
  invFun := sphereMap f.symm
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv x := Subtype.ext (f.apply_symm_apply x)
  continuous_toFun := sphereMap_continuous f
  continuous_invFun := sphereMap_continuous f.symm

theorem toSphere_preserving (f : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereMap f) (volume : Measure E).toSphere
      (volume : Measure E).toSphere := by
  have hm := (sphereMap_continuous f).measurable
  refine ⟨hm, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' _ (hs.preimage hm),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : Ioo (0:ℝ) 1 • (Subtype.val '' (sphereMap f ⁻¹' s)) =
      f ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r,hr,y,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨r,hr,f z,⟨sphereMap f z,hz,rfl⟩,by simp⟩
    · rintro ⟨r,hr,y,⟨z,hz,rfl⟩,hxy⟩
      refine ⟨r,hr,f.symm z,⟨sphereMap f.symm z,?_,rfl⟩,?_⟩
      · change sphereMap f (sphereMap f.symm z) ∈ s
        convert hz using 1
        apply Subtype.ext
        exact f.apply_symm_apply z
      · apply f.injective
        simpa only [map_smul, f.apply_symm_apply] using hxy
  rw [hcone]
  have hp := congrArg (fun μ : Measure E => μ (Ioo (0:ℝ) 1 • (Subtype.val '' s)))
    f.measurePreserving.map_eq
  change (Measure.map f.toMeasurableEquiv volume) _ = _ at hp
  rw [f.toMeasurableEquiv.map_apply] at hp
  exact hp

/-- Uniform probability on the unit sphere, obtained by normalizing spherical Haar measure. -/
def uniformSphere (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Measure (sphere (0:E) 1) :=
  ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere

instance [Nontrivial E] : IsProbabilityMeasure (uniformSphere E) := by
  unfold uniformSphere
  have : NeZero (volume : Measure E).toSphere := ⟨Measure.toSphere_ne_zero volume⟩
  infer_instance

theorem uniformSphere_preserving (f : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereMap f) (uniformSphere E) (uniformSphere E) := by
  exact (toSphere_preserving f).smul_measure _

theorem uniformSphere_integral_isometry (f : E ≃ₗᵢ[ℝ] E)
    (g : sphere (0:E) 1 → ℝ) :
    (∫ x, g (sphereMap f x) ∂uniformSphere E) = ∫ x, g x ∂uniformSphere E := by
  exact (uniformSphere_preserving f).integral_comp (sphereHomeomorph f).measurableEmbedding g

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
local notation "V" => EuclideanSpace ℝ d
local notation "Sph" => sphere (0:V) 1

omit [DecidableEq d] in
private theorem sphere_coord_pair_integrable (i j : d) :
    Integrable (fun x : Sph => x.val i * x.val j) (uniformSphere V) := by
  have hc : Continuous (fun x : Sph => x.val i * x.val j) := by fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [Nonempty d] in
theorem uniformSphere_coord_cross {i j : d} (hij : i≠j) :
    (∫ x : Sph, x.val i * x.val j ∂uniformSphere V) = 0 := by
  let f : V ≃ₗᵢ[ℝ] V := LinearIsometryEquiv.piLpCongrRight 2
    (fun k : d => if k=i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have he := uniformSphere_integral_isometry f (fun x : Sph => x.val i * x.val j)
  have hf (x : Sph) : (sphereMap f x).val i * (sphereMap f x).val j =
      -(x.val i * x.val j) := by
    simp [sphereMap, f, hij.symm]
  simp_rw [hf, integral_neg] at he
  linarith

omit [Nonempty d] in
theorem uniformSphere_coord_square_eq (i j : d) :
    (∫ x : Sph, (x.val i)^2 ∂uniformSphere V) =
      ∫ x : Sph, (x.val j)^2 ∂uniformSphere V := by
  let f := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have he := uniformSphere_integral_isometry f (fun x : Sph => (x.val i)^2)
  have hf (x : Sph) : (sphereMap f x).val i = x.val j := by
    simp [sphereMap, f, Equiv.piCongrLeft']
  simpa only [hf] using he.symm

theorem uniformSphere_coord_square (i : d) :
    (∫ x : Sph, (x.val i)^2 ∂uniformSphere V) = 1 / (Fintype.card d:ℝ) := by
  have hnorm (x : Sph) : ∑ j, (x.val j)^2 = (1:ℝ) := by
    simpa only [EuclideanSpace.sphere_zero_eq 1 (by norm_num), Set.mem_ofPred_eq, one_pow]
      using x.property
  have hi (j : d) : Integrable (fun x : Sph => (x.val j)^2) (uniformSphere V) := by
    simpa only [sq] using sphere_coord_pair_integrable j j
  have hh : (Fintype.card d:ℝ) * (∫ x : Sph, (x.val i)^2 ∂uniformSphere V) = 1 := by
    calc
      _ = ∑ j, ∫ x : Sph, (x.val j)^2 ∂uniformSphere V := by
        simp_rw [uniformSphere_coord_square_eq (d:=d) _ i]
        simp
      _ = ∫ x : Sph, ∑ j, (x.val j)^2 ∂uniformSphere V :=
        (integral_finsetSum _ (fun j _ => hi j)).symm
      _ = 1 := by simp [hnorm]
  exact (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card d:ℝ)≠0)).mpr
    (by nlinarith [hh])

theorem uniformSphere_coord_pair (i j : d) :
    (∫ x : Sph, x.val i * x.val j ∂uniformSphere V) =
      if i=j then 1/(Fintype.card d:ℝ) else 0 := by
  by_cases h : i=j
  · subst j
    simpa only [ite_true, sq] using uniformSphere_coord_square (d:=d) i
  · rw [ite_eq_right_iff.mpr (fun h' => (h h').elim)]
    exact uniformSphere_coord_cross h

/-- A genuine uniform unit vector has identity covariance divided by dimension. -/
theorem uniformSphere_matrix_norm_sq (M : Matrix d d ℝ) :
    (∫ x : Sph, ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp x.val))‖^2 ∂uniformSphere V) =
      hsSq M / (Fintype.card d:ℝ) := by
  have hint (i j k : d) : Integrable
      (fun x : Sph => (M i j*M i k)*(x.val j*x.val k)) (uniformSphere V) :=
    (sphere_coord_pair_integrable j k).const_mul _
  have heq (x : Sph) : ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp x.val))‖^2 =
      ∑ i, ∑ j, ∑ k, (M i j*M i k)*(x.val j*x.val k) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mulVec, dotProduct, sq, Finset.sum_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [heq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_finsetSum _ (fun k _ => hint i j k)))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint _ j k)),
    integral_finsetSum _ (fun k _ => hint _ _ k), integral_const_mul,
    uniformSphere_coord_pair]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [hsSq, ← Finset.sum_div, sq, mul_one_div]

theorem uniformSphere_hsNorm_identity (M : Matrix d d ℝ) :
    (∫ x : Sph, ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp x.val))‖^2 ∂uniformSphere V) =
      (hsNorm M)^2 / (Fintype.card d:ℝ) := by
  rw [uniformSphere_matrix_norm_sq, hsNorm_sq]

end
end chebyshev1.Stochastic
