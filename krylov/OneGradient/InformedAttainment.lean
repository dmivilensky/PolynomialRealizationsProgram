import krylov.OneGradient.InformedCompression
import krylov.Correction.PlanarAttainment
import krylov.LinearAlgebra.SymmetricBall
import krylov.Reference.CanonicalSteps
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), actual informed leading-operator sharpness.
Use: construct genuine symmetric canonical increments, hidden-base prior
and output defect attaining the full original K_X(c), including zero budgets.
Source: existing trace-zero planar witnesses, exact aggregate actions and
the proved attained symmetric-ball residual identity.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.LinearAlgebra krylov.Correction krylov.Reference
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} {n : ℕ}

/-- Genuine symmetric canonical matrices attain the full original
known-base leading-operator bound with every individual increment budget,
the actual base-prior budget and actual independent output-defect budget.
Use: the exact K_X(c) operator upper bound has true matrix witnesses;
zero, empty and corner profiles use the same construction.
Article: main_krylov, thm:local(b).
Proof: choose an actual scalar maximizer and its complementary coordinate.
The existing trace-zero planar increments give all three exact aggregate
actions. A genuine rank-one base perturbation gives the actual hidden
pivot c. The true attained symmetric-ball identity supplies an actual
output operator aligned with the whole correlated residual and input;
the real isometric matrix dictionary constructs its symmetric matrix. -/
theorem informed_compression_attained_rank_one (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i,(K i).HasOrthogonalProjection]
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (heK : ∀ i∈I,e∈K i) (hhK : ∀ i∈I,h∈(K i)ᗮ)
    (omega : ι → ℝ) (homega : ∀ i∈I,0≤ omega i) (w c : ℝ) (hw : 0≤ w) (hc : 0≤ c) :
    ∃ D : ι → Matrix (Fin n) (Fin n) ℝ, ∃ R F : Matrix (Fin n) (Fin n) ℝ,
      (∀ i∈I,(D i).IsSymm ∧ ‖D i‖≤ omega i) ∧ R.IsSymm ∧ ‖R‖≤ c ∧
      cgOperator R=c • InnerProductSpace.rankOne ℝ h h ∧ F.IsSymm ∧ ‖F‖≤ w ∧
      let T := fun i => cgOperator (D i)
      let X := ∑ i∈I,(K i).starProjection (T i h)
      let q := inner ℝ h (cgOperator R h)+∑ i∈I,inner ℝ h (T i h)
      ‖(∑ i∈I,(K i).starProjection (T i ((K i).starProjection X)))+cgOperator F (X+q • h)‖=
        informedConstant (∑ i∈I,omega i) w c := by
  let W := ∑ i∈I,omega i
  have hW : 0≤ W := sum_nonneg homega
  obtain ⟨a,ha,hmax⟩ := (informedConstant_variational W w c).1
  let s := Real.sqrt (1-a^2)
  have hs : 0≤ s := Real.sqrt_nonneg _
  have hcircle : s^2+a^2=1 := by
    have hsquare := Real.sq_sqrt (by nlinarith [ha.1,ha.2] : 0≤1-a^2)
    change (Real.sqrt (1-a^2))^2+a^2=1
    linarith
  let D := fun i => planarMatrix e h (omega i*(-s)) (omega i*a) (omega i*s)
  let R := planarMatrix h e c 0 0
  let T := fun i => cgOperator (D i)
  let X := ∑ i∈I,(K i).starProjection (T i h)
  let YX := ∑ i∈I,(K i).starProjection (T i ((K i).starProjection X))
  let q := inner ℝ h (cgOperator R h)+∑ i∈I,inner ℝ h (T i h)
  have hv := planar_aggregate_values I K e h he hh heh heK hhK omega (-s) a s
  have hX : X=(W*a) • e := hv.1
  have hY : YX=(W^2*(-s)*a) • e := hv.2.1
  have hhe : inner ℝ h e=0 := (real_inner_comm e h).trans heh
  have hRh : inner ℝ h (cgOperator R h)=c := by
    have hhh : inner ℝ h h=1 := by rw [real_inner_self_eq_norm_sq,hh,one_pow]
    rw [show cgOperator R h=(c*inner ℝ h h) • h from by
      change Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix h e c 0 0) h=_
      rw [planarMatrix_action]
      simp only [zero_mul,add_zero,zero_smul]]
    rw [hhh,mul_one,real_inner_smul_right,hhh,mul_one]
  have hgamma : (∑ i∈I,inner ℝ h (T i h))=W*s := hv.2.2
  have hq : q=c+W*s := by rw [show q=inner ℝ h (cgOperator R h)+∑ i∈I,inner ℝ h (T i h) from rfl,hRh,hgamma]
  have hYn : ‖YX‖=a*W^2*s := by
    rw [hY,norm_smul,he,mul_one,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg W),abs_neg,
      abs_of_nonneg hs,abs_of_nonneg ha.1]
    ring
  have hVn : ‖X+q • h‖=Real.sqrt (a^2*W^2+(c+W*s)^2) := by
    rw [hX,hq,← Real.sqrt_sq (norm_nonneg _),planar_coordinates_norm_sq e h he hh heh]
    congr 1
    ring
  obtain ⟨Fop,hFs,hFn,hFe⟩ := symmetric_residual_attained YX (X+q • h) hw
  let F := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm Fop
  have hFop : cgOperator F=Fop := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _
  refine ⟨D,R,F,?_,planarMatrix_isSymm _ _ _ _ _,?_,?_,?_,?_,?_⟩
  · intro i hi
    refine ⟨planarMatrix_isSymm _ _ _ _ _,?_⟩
    change chebyshev1.opNorm (planarMatrix e h (omega i*(-s)) (omega i*a) (omega i*s))≤ omega i
    rw [planarMatrix_scale,chebyshev1.opNorm_smul,abs_of_nonneg (homega i hi)]
    exact (mul_le_mul_of_nonneg_left (planar_spectral_norm_le e h he hh heh s a hcircle)
      (homega i hi)).trans_eq (mul_one _)
  · exact (spectral_le_hsNorm R).trans (planar_terminal_hsNorm h e hh he hhe hc).le
  · apply ContinuousLinearMap.ext
    intro v
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix h e c 0 0) v=_
    rw [planarMatrix_action]
    simp only [zero_mul,add_zero,zero_smul,_root_.smul_apply,InnerProductSpace.rankOne_apply,smul_smul]
  · apply Matrix.isHermitian_iff_isSymm.mp
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    change (cgOperator F).toLinearMap.IsSymmetric
    rw [hFop]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hFs
  · rw [← Matrix.l2_opNorm_toEuclideanCLM]
    change ‖cgOperator F‖≤ w
    rw [hFop]
    exact hFn
  · change ‖YX+cgOperator F (X+q • h)‖=informedConstant W w c
    rw [hFop,hFe,hYn,hVn]
    exact hmax

/-- Genuine symmetric matrices attain the full informed constant with every
original individual budget, including all zero and corner profiles.
Use: the original operator sharpness API remains available independently
of the stronger rank-one prior realization used by physical scenarios.
Article: main_krylov, thm:local(b).
Proof: use the stronger exact rank-one prior attainer and forget only its
additional canonical-prior identity. -/
theorem informed_compression_attained (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i,(K i).HasOrthogonalProjection]
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (heK : ∀ i∈I,e∈K i) (hhK : ∀ i∈I,h∈(K i)ᗮ)
    (omega : ι → ℝ) (homega : ∀ i∈I,0≤ omega i) (w c : ℝ) (hw : 0≤ w) (hc : 0≤ c) :
    ∃ D : ι → Matrix (Fin n) (Fin n) ℝ, ∃ R F : Matrix (Fin n) (Fin n) ℝ,
      (∀ i∈I,(D i).IsSymm ∧ ‖D i‖≤ omega i) ∧ R.IsSymm ∧ ‖R‖≤ c ∧
      F.IsSymm ∧ ‖F‖≤ w ∧
      let T := fun i => cgOperator (D i)
      let X := ∑ i∈I,(K i).starProjection (T i h)
      let q := inner ℝ h (cgOperator R h)+∑ i∈I,inner ℝ h (T i h)
      ‖(∑ i∈I,(K i).starProjection (T i ((K i).starProjection X)))+cgOperator F (X+q • h)‖=
        informedConstant (∑ i∈I,omega i) w c := by
  obtain ⟨D,R,F,hD,hR,hRn,hRform,hF,hFn,hvalue⟩ :=
    informed_compression_attained_rank_one I K e h he hh heh heK hhK omega homega w c hw hc
  exact ⟨D,R,F,hD,hR,hRn,hF,hFn,hvalue⟩

end
end krylov.OneGradient
