import krylov.LinearAlgebra.HiddenEntry
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Article: main_krylov, thm:C2(c), boundary-inclusive completion width.
Use: bound the true hidden scalar uncertainty from the observed cross
block without an invertible endpoint resolvent or a strict interior gap.
Source: symmetric spectral-ball quadratic inequalities, actual orthogonal
one-dimensional decomposition and the source's Schur-completion geometry.
-/

namespace krylov.LinearAlgebra
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine spectral contraction has its real quadratic form in the exact unit interval scaled by the squared input norm.
Use: both shifted completion tests hold at singular endpoint blocks as well as in the interior.
Article: main_krylov, thm:C2(c), −‖v‖²≤⟨v,Tv⟩≤‖v‖².
Proof: real Cauchy–Schwarz and the actual operator norm bound control the absolute quadratic form. -/
theorem contraction_quadratic_bound (T : E →L[ℝ] E) (hT : ‖T‖≤1) (v : E) :
    |inner ℝ v (T v)|≤‖v‖^2 := by
  have ht : ‖T v‖≤‖v‖ := ((T.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg v))).trans_eq (one_mul _)
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left ht (norm_nonneg v)).trans_eq (pow_two _).symm)

/-- A genuine symmetric operator vanishing on a unit vector's orthogonal hyperplane is exactly its scalar rank-one action.
Use: the only unknown completion coordinate is derived from the actual observed hyperplane rather than assumed.
Article: main_krylov, thm:C2(c), T=⟨v₀,Tv₀⟩v₀v₀ᵀ.
Proof: decompose every input into its true normal and perpendicular parts.
The latter is annihilated. Symmetry identifies the normal image against
every test vector, and the inner-product extensionality theorem gives the result.
-/
theorem symmetric_hyperplane_annihilator (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)
    (v : E) (hv : ‖v‖=1) (hzero : ∀ u : E, inner ℝ v u=0 → T u=0) :
    ∀ u : E, T u=(inner ℝ v u*inner ℝ v (T v)) • v := by
  -- Decompose each actual input before identifying the image of the true unit normal.
  change ∀ x y, inner ℝ (T x) y=inner ℝ x (T y) at hT
  have hvv : inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hv,one_pow]
  have hdecomp (u : E) : T u=(inner ℝ v u) • T v := by
    have hz := hzero (u-(inner ℝ v u) • v) (by simp only [inner_sub_right,real_inner_smul_right,hvv,mul_one,sub_self])
    rw [map_sub,map_smul,sub_eq_zero] at hz
    exact hz
  have hTv : T v=(inner ℝ v (T v)) • v := by
    apply ext_inner_left ℝ
    intro u
    rw [real_inner_smul_right]
    calc
      inner ℝ u (T v) = inner ℝ (T u) v := (hT u v).symm
      _ = inner ℝ v u*inner ℝ (T v) v := by rw [hdecomp,real_inner_smul_left]
      _ = _ := by rw [real_inner_comm v (T v),real_inner_comm u v]; ring
  intro u
  rw [hdecomp]
  conv_lhs => rw [hTv,smul_smul]

/-- Two genuine symmetric unit-ball completions of the same observed hyperplane differ in their hidden normal diagonal by at most 2(1−‖x‖²), including singular boundary cases.
Use: the midpoint consistency-interval half-width has the exact source upper bound without any unproved boundary limit.
Article: main_krylov, thm:C2(c), half-width≤1−‖x‖².
Proof: the actual common cross vector is perpendicular to the unit normal.
Both completions act on it exactly as the known restriction, so symmetry
identifies both cross pairings with ‖x‖². Apply the true spectral quadratic
bounds to v₀+x and v₀−x. Their common lower-block quadratic term cancels,
leaving the exact hidden-diagonal diameter estimate at every boundary.
-/
theorem completion_diagonal_diameter (S T R : E →L[ℝ] E)
    (hS : S.toLinearMap.IsSymmetric) (hT : T.toLinearMap.IsSymmetric)
    (hR : R.toLinearMap.IsSymmetric) (hSn : ‖S‖≤1) (hTn : ‖T‖≤1)
    (v : E) (hv : ‖v‖=1)
    (hSR : ∀ u : E, inner ℝ v u=0 → S u=R u)
    (hTR : ∀ u : E, inner ℝ v u=0 → T u=R u) :
    let x := R v-(inner ℝ v (R v)) • v
    inner ℝ v (S v)-inner ℝ v (T v)≤2*(1-‖x‖^2) := by
  -- All cross and lower-block terms are fixed by the actual observed hyperplane action.
  change ∀ x y, inner ℝ (S x) y=inner ℝ x (S y) at hS
  change ∀ x y, inner ℝ (T x) y=inner ℝ x (T y) at hT
  change ∀ x y, inner ℝ (R x) y=inner ℝ x (R y) at hR
  let x := R v-(inner ℝ v (R v)) • v
  have hvv : inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hv,one_pow]
  have hvx : inner ℝ v x=0 := by simp only [x,inner_sub_right,real_inner_smul_right,hvv,mul_one,sub_self]
  have hxv : inner ℝ x v=0 := (real_inner_comm v x).trans hvx
  have hRx : inner ℝ x (R v)=‖x‖^2 := by
    have hh : inner ℝ x x=inner ℝ x (R v) := by
      conv_lhs => rw [show x=R v-(inner ℝ v (R v)) • v from rfl]
      rw [inner_sub_right,real_inner_smul_right,hxv,mul_zero,sub_zero]
    rw [real_inner_self_eq_norm_sq] at hh
    exact hh.symm
  have hSx : S x=R x := hSR x hvx
  have hTx : T x=R x := hTR x hvx
  have hcrossS : inner ℝ x (S v)=‖x‖^2 := by
    rw [← hS x v,hSx,hR x v]
    exact hRx
  have hcrossT : inner ℝ x (T v)=‖x‖^2 := by
    rw [← hT x v,hTx,hR x v]
    exact hRx
  have hnormp : ‖v+x‖^2=1+‖x‖^2 := by rw [norm_add_sq_real,hv,one_pow,hvx]; ring
  have hnormm : ‖v-x‖^2=1+‖x‖^2 := by rw [norm_sub_sq_real,hv,one_pow,hvx]; ring
  have hp := (abs_le.mp (contraction_quadratic_bound S hSn (v+x))).2
  have hm := (abs_le.mp (contraction_quadratic_bound T hTn (v-x))).1
  rw [hnormp] at hp
  rw [hnormm] at hm
  simp only [map_add,map_sub,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right] at hp hm
  have hcrossS' : inner ℝ v (S x)=‖x‖^2 :=
    (hS v x).symm.trans ((real_inner_comm x (S v)).trans hcrossS)
  have hcrossT' : inner ℝ v (T x)=‖x‖^2 :=
    (hT v x).symm.trans ((real_inner_comm x (T v)).trans hcrossT)
  rw [hcrossS,hcrossS',hSx] at hp
  rw [hcrossT,hcrossT',hTx] at hm
  change _≤2*(1-‖x‖^2)
  linarith


/-- Every two genuine symmetric unit-ball completions of the same observed hyperplane have their quadratic-form diameter bounded by the exact hidden-entry width in any unit direction.
Use: the computable source midpoint concerns the original CG diagonal, which need not equal the actual unobserved normal direction.
Article: main_krylov, thm:C2(c), |q₊−q₋|≤2(1−‖x‖²).
Proof: the genuine difference is symmetric and vanishes on the observed
hyperplane, so its exact derived action is rank one along the unit normal.
The two signed normal-diagonal estimates bound its absolute scalar. The
original unit direction contributes only its squared normal pairing, at
most one by real Cauchy–Schwarz. Singular endpoint completions are included.
-/
theorem completion_quadratic_diameter (S T R : E →L[ℝ] E)
    (hS : S.toLinearMap.IsSymmetric) (hT : T.toLinearMap.IsSymmetric)
    (hR : R.toLinearMap.IsSymmetric) (hSn : ‖S‖≤1) (hTn : ‖T‖≤1)
    (v e : E) (hv : ‖v‖=1) (he : ‖e‖=1)
    (hSR : ∀ u : E, inner ℝ v u=0 → S u=R u)
    (hTR : ∀ u : E, inner ℝ v u=0 → T u=R u) :
    let x := R v-(inner ℝ v (R v)) • v
    |inner ℝ e (S e)-inner ℝ e (T e)|≤2*(1-‖x‖^2) := by
  -- Derive the exact rank-one difference from the actual common observed hyperplane.
  let d := inner ℝ v (S v)-inner ℝ v (T v)
  let x := R v-(inner ℝ v (R v)) • v
  have hd : |d|≤2*(1-‖x‖^2) := abs_le.mpr ⟨by
    have hh := completion_diagonal_diameter T S R hT hS hR hTn hSn v hv hTR hSR
    change _≤2*(1-‖x‖^2) at hh
    dsimp only [d]
    linarith,
    completion_diagonal_diameter S T R hS hT hR hSn hTn v hv hSR hTR⟩
  have hD : (S-T).toLinearMap.IsSymmetric := hS.sub hT
  have hzero (u : E) (hu : inner ℝ v u=0) : (S-T) u=0 := by
    simp only [_root_.sub_apply,hSR u hu,hTR u hu,sub_self]
  have haction := symmetric_hyperplane_annihilator (S-T) hD v hv hzero e
  have hvalue : inner ℝ e (S e)-inner ℝ e (T e)=d*(inner ℝ v e)^2 := by
    rw [← inner_sub_right,← _root_.sub_apply,haction,real_inner_smul_right]
    simp only [_root_.sub_apply,inner_sub_right]
    rw [real_inner_comm v e]
    dsimp only [d]
    ring
  have hc : (inner ℝ v e)^2≤1 := by
    have hh := abs_real_inner_le_norm v e
    rw [hv,he,mul_one] at hh
    nlinarith [sq_abs (inner ℝ v e),abs_nonneg (inner ℝ v e)]
  change _≤2*(1-‖x‖^2)
  rw [hvalue,abs_mul,abs_sq]
  exact (mul_le_mul_of_nonneg_left hc (abs_nonneg d)).trans_eq (mul_one |d|) |>.trans hd

end
end krylov.LinearAlgebra
