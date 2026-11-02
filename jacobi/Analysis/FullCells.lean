import jacobi.Analysis.CellEmbedding
import jacobi.Reference.WeightedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: jacobi, Theorem C.5.
The actual N physical cells are the printed intervals [i/N,(i+1)/N).
Their exact Lebesgue measures and disjointness give a genuine linear
isometry from the finite Euclidean space into the original L2 interval.
Source: the existing cellEmbedding norm theorem and mathlib subtype measure.
Use: fullStepIsometry is precisely the original U_N in Theorem 2.1.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The article's actual full physical cell, with its exact half-open
endpoint convention and true matrix dimension N=n+1.
Use: fullStepIsometry is precisely the original U_N in Theorem 2.1.
Article: jacobi, Theorem C.5.
-/
def fullCell (n:ℕ) (i:Fin (n+1)) : Set Interval :=
  {t | (i.val:ℝ)/((n:ℝ)+1)≤(t:ℝ) ∧ (t:ℝ)<((i.val:ℝ)+1)/((n:ℝ)+1)}

/-- Every genuine original full cell is measurable.
Use: its actual cell indicator defines a vector in the same L2 space.
Article: jacobi, Theorem C.5.
Proof: the two physical coordinate inequalities are measurable. -/
theorem fullCell_measurable (n:ℕ) (i:Fin (n+1)) : MeasurableSet (fullCell n i) :=
  (measurableSet_le measurable_const measurable_subtype_coe).inter
    (measurableSet_lt measurable_subtype_coe measurable_const)

/-- Every original full physical cell has exactly its true width 1/N.
Use: the genuine step embedding preserves the original Euclidean norm.
Article: jacobi, Theorem C.5.
Proof: the coordinate image is the original real Ico interval inside
[0,1]; subtype Lebesgue measure and its exact interval formula apply. -/
theorem fullCell_volume (n:ℕ) (i:Fin (n+1)) :
    (volume:Measure Interval).real (fullCell n i)=1/((n:ℝ)+1) := by
  -- Compute the original coordinate image before passing to subtype measure.
  have hm : MeasurableEmbedding (Subtype.val:Interval→ℝ) := MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hi : (i.val:ℝ)+1≤(n:ℝ)+1 := by exact_mod_cast i.isLt
  have he : Subtype.val '' fullCell n i=Ico ((i.val:ℝ)/((n:ℝ)+1)) (((i.val:ℝ)+1)/((n:ℝ)+1)) := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro hx
      have hu : ((i.val:ℝ)+1)/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr hi
      exact ⟨⟨x,⟨(by positivity : (0:ℝ)≤(i.val:ℝ)/((n:ℝ)+1)).trans hx.1,hx.2.le.trans hu⟩⟩,hx,rfl⟩
  unfold Measure.real
  rw [Measure.Subtype.volume_def,hm.comap_apply,he,Real.volume_Ico]
  rw [show ((i.val:ℝ)+1)/((n:ℝ)+1)-(i.val:ℝ)/((n:ℝ)+1)=1/((n:ℝ)+1) by ring,
    ENNReal.toReal_ofReal (by positivity)]

/-- Distinct actual full physical cells are disjoint, also at their
shared endpoints with the original Ico convention.
Use: the exact embedding norm contains no mixed-cell contribution.
Article: jacobi, Theorem 2.1.
Proof: the earlier cell ends no later than the later cell begins. -/
theorem fullCell_disjoint (n:ℕ) : Pairwise (fun i j:Fin (n+1) => Disjoint (fullCell n i) (fullCell n j)) := by
  -- Order the two genuine cell indices to separate their shared physical boundary.
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h : (i.val:ℝ)+1≤(j.val:ℝ) := by exact_mod_cast hlt
    have hd := (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr h
    exact (not_lt_of_ge (hd.trans hj.1)) hi.2
  · have h : (j.val:ℝ)+1≤(i.val:ℝ) := by exact_mod_cast hgt
    have hd := (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr h
    exact (not_lt_of_ge (hd.trans hi.1)) hj.2

/-- The original step map as a genuine real linear map into the same
physical L2 space used by the continuum operator.
Use: fullStepIsometry adds its exact proved norm preservation.
Article: jacobi, Theorem 2.1.
-/
def fullStepLinear (n:ℕ) : EuclideanSpace ℝ (Fin (n+1))→ₗ[ℝ] Space where
  toFun v := ∑i:Fin (n+1), (sqrt ((n:ℝ)+1)*v i) •
    indicatorConstLp 2 (fullCell_measurable n i) (measure_ne_top _ _) (1:ℝ)
  map_add' v w := by simp only [PiLp.add_apply,mul_add,add_smul,Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [PiLp.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [show sqrt ((n:ℝ)+1)*(c*v i)=c*(sqrt ((n:ℝ)+1)*v i) by ring]

/-- The original linear step map is exactly the earlier actual finite
cell embedding with its source sqrt(N) coefficient normalization.
Use: fullStepIsometry reuses the existing exact disjoint-cell norm
identity instead of proving a separate approximate quadrature formula.
Article: jacobi, Theorem 2.1.
Proof: the existing cellEmbedding_sum_smul identity is the same finite
sum of the original physical cell indicators. -/
theorem fullStepLinear_eq (n:ℕ) (v:EuclideanSpace ℝ (Fin (n+1))) :
    fullStepLinear n v=cellEmbedding (fullCell n) (fullCell_measurable n)
      (fun _ => measure_ne_top _ _) (fun i => sqrt ((n:ℝ)+1)*v i) :=
  (cellEmbedding_sum_smul (fullCell n) (fullCell_measurable n) (fun _ => measure_ne_top _ _)
    (fun i => sqrt ((n:ℝ)+1)*v i)).symm

/-- The article's original step embedding is a genuine linear isometry
with precisely its printed physical cells and normalization.
Use: the embedded finite inverse in Theorem 2.1 is U_N*(2*N^2*(I-J_N))^(-1)*U_N^*;
its actual embedded eigenvectors are therefore unit vectors.
Article: jacobi, Theorem 2.1.
Proof: the proved exact cell norm is 1/N times the sum of the squared
sqrt(N) coefficients, hence equals the actual Euclidean norm squared. -/
def fullStepIsometry (n:ℕ) : EuclideanSpace ℝ (Fin (n+1))→ₗᵢ[ℝ] Space where
  toLinearMap := fullStepLinear n
  norm_map' v := by
    have hs := cellEmbedding_norm_sq (fullCell n) (fullCell_measurable n)
      (fun _ => measure_ne_top _ _) (fullCell_disjoint n) (fullCell_volume n)
      (fun i => sqrt ((n:ℝ)+1)*v i)
    rw [← fullStepLinear_eq] at hs
    simp_rw [mul_pow,sq_sqrt (by positivity : (0:ℝ)≤(n:ℝ)+1)] at hs
    rw [← Finset.mul_sum,← mul_assoc,one_div_mul_cancel (by positivity : (n:ℝ)+1≠0),
      one_mul,← EuclideanSpace.real_norm_sq_eq] at hs
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

end
end jacobi.Analysis
