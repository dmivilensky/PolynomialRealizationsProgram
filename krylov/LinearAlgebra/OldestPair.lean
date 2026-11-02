import krylov.LinearAlgebra.NormalizedRankOne
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Article: main_krylov, apG:mss, exact geometry of the oldest pair.
Use: the amplification of the oldest diagonal is determined by its actual
distance to the span of the newer normalized columns.
Source: inverse-transpose dual coordinates, orthogonal distance and Cauchy--Schwarz.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- An actual matrix column viewed in its genuine Euclidean space.
Use: the oldest/newer span is formed from the actual normalized observation columns.
Article: main_krylov, apG:mss, û_i. -/
def euclideanColumn (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i : Fin (n+1)) :
    EuclideanSpace ℝ (Fin (n+1)) := WithLp.toLp 2 (fun a => V a i)

/-- The actual inverse-transpose coordinate vector dual to the oldest column.
Use: this vector is the precise rank-one amplifier of the oldest diagonal error.
Article: main_krylov, apG:mss, b=Û^(−T)e₀. -/
def oldestDual (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (Vᵀ⁻¹*ᵥ Pi.single 0 1)

/-- The actual span of the newer columns, with the oldest column removed.
Use: define the source distance geometrically, independently of inverse norms.
Article: main_krylov, apG:mss, span{û₁,…,û_(n−1)}. -/
def newerColumnSpan (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))) :=
  Submodule.span ℝ (Set.range fun i : Fin n => euclideanColumn V i.succ)

/-- Actual matrix action is the actual linear combination of its Euclidean columns.
Use: identify the newer span from the vanishing oldest inverse coordinate.
Article: main_krylov, apG:mss, column-coordinate expansion.
Proof: each coordinate is the same finite matrix-vector product sum. -/
theorem euclidean_column_expansion (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (a : Fin (n+1) → ℝ) :
    WithLp.toLp 2 (V*ᵥ a)=∑ i, a i • euclideanColumn V i := by
  ext j
  simp only [Matrix.mulVec, dotProduct, euclideanColumn, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The genuine oldest dual extracts the oldest coordinate after the actual matrix action.
Use: prove duality with every actual column without an assumed dual basis.
Article: main_krylov, apG:mss, bᵀÛa=a₀.
Proof: move the actual inverse transpose through the pairing and cancel Û⁻¹Û. -/
theorem oldestDual_pair_action (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hV : IsUnit V.det) (a : Fin (n+1) → ℝ) :
    inner ℝ (oldestDual V) (WithLp.toLp 2 (V*ᵥ a))=a 0 := by
  have ht : IsUnit Vᵀ.det := by simpa only [det_transpose] using hV
  simp only [oldestDual, EuclideanSpace.inner_toLp_toLp, star_trivial, transpose_pairing,
    mulVec_mulVec, mul_nonsing_inv _ ht, one_mulVec, dotProduct_single, mul_one]

/-- The actual oldest dual has pairing one with its own column and zero with every newer column.
Use: isolates exactly the oldest-pair contribution in the model error.
Article: main_krylov, apG:mss, dual-vector pairings.
Proof: specialize the proved actual coordinate extraction to a coordinate unit vector. -/
theorem oldestDual_pair_column (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hV : IsUnit V.det) (i : Fin (n+1)) :
    inner ℝ (oldestDual V) (euclideanColumn V i)=if i=0 then 1 else 0 := by
  have he := oldestDual_pair_action V hV (Pi.single i 1)
  rw [mulVec_single_one] at he
  change inner ℝ (oldestDual V) (euclideanColumn V i)=((Pi.single i (1 : ℝ) : Fin (n+1) → ℝ) 0) at he
  simpa only [Pi.single_apply, eq_comm] using he

/-- The actual newer-column span is exactly the orthogonal hyperplane of the actual oldest dual.
Use: no independence or distance property is hidden in a geometric model field.
Article: main_krylov, apG:mss, orthogonality to the newer span.
Proof: each newer column is annihilated; conversely, the actual inverse coordinates
reconstruct a vector using only newer columns when its oldest dual pairing vanishes. -/
theorem newerColumnSpan_iff (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hV : IsUnit V.det) (w : EuclideanSpace ℝ (Fin (n+1))) :
    w ∈ newerColumnSpan V ↔ inner ℝ (oldestDual V) w=0 := by
  -- Establish annihilation first, then reconstruct the vector using its actual inverse coordinates.
  have hle : newerColumnSpan V ≤ (innerSL ℝ (oldestDual V)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ (oldestDual V) (euclideanColumn V i.succ)=0
    rw [oldestDual_pair_column V hV, ite_eq_right (Fin.succ_ne_zero i)]
  constructor
  · exact fun h => hle h
  · intro hw
    let a := V⁻¹*ᵥ WithLp.ofLp w
    have ha : WithLp.toLp 2 (V*ᵥ a)=w := by
      simp only [a, mulVec_mulVec, mul_nonsing_inv _ hV, one_mulVec, WithLp.toLp_ofLp]
    have hz : a 0=0 := by rw [← oldestDual_pair_action V hV a, ha, hw]
    have he := euclidean_column_expansion V a
    rw [ha, Fin.sum_univ_succ, hz, zero_smul, zero_add] at he
    rw [he]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)

/-- The actual oldest dual is nonzero for every actual invertible window.
Use: all inverse-distance normalizations are justified before division.
Article: main_krylov, apG:mss, Δ>0.
Proof: its proved pairing with the oldest actual column is one. -/
theorem oldestDual_ne_zero (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hV : IsUnit V.det) :
    oldestDual V≠0 := by
  intro hz
  have he := oldestDual_pair_column V hV 0
  exact (zero_ne_one : (0 : ℝ)≠1) (by simpa only [hz, inner_zero_left, ite_true] using he)

/-- The genuine distance from the oldest column to the actual newer span is its reciprocal dual norm.
Use: proves the exact amplification Δ⁻² of the oldest-pair diagonal contribution.
Article: main_krylov, apG:mss, ‖b‖=Δ⁻¹.
Proof: subtract the explicit normal component ‖b‖⁻²b to attain the distance;
Cauchy--Schwarz bounds the distance to every other vector in the actual newer span. -/
theorem oldest_column_distance (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hV : IsUnit V.det) :
    Metric.infDist (euclideanColumn V 0) (newerColumnSpan V : Set _) = ‖oldestDual V‖⁻¹ := by
  -- The explicit normal component constructs a closest vector in the actual newer span.
  let b := oldestDual V
  let u := euclideanColumn V 0
  have hb : 0<‖b‖ := norm_pos_iff.mpr (oldestDual_ne_zero V hV)
  have hu : inner ℝ b u=1 := by simpa only [ite_true] using oldestDual_pair_column V hV 0
  have hm : u-(‖b‖^2)⁻¹ • b ∈ newerColumnSpan V := by
    apply (newerColumnSpan_iff V hV _).mpr
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu,
      inv_mul_cancel₀ (pow_ne_zero 2 hb.ne'), sub_self]
  have hn : ‖u-(u-(‖b‖^2)⁻¹ • b)‖=‖b‖⁻¹ := by
    rw [sub_sub_cancel, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    field_simp
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem hm).trans_eq (by simpa only [dist_eq_norm] using hn)
  · apply (Metric.le_infDist ⟨0, (newerColumnSpan V).zero_mem⟩).mpr
    intro y hy
    have hy0 := (newerColumnSpan_iff V hV y).mp hy
    have hc := norm_inner_le_norm (𝕜 := ℝ) b (u-y)
    rw [inner_sub_right, hy0, hu, sub_zero, norm_one] at hc
    rw [dist_eq_norm]
    rw [← one_div]
    change 1/‖b‖≤‖u-y‖
    exact (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hc)

end
end krylov.LinearAlgebra
