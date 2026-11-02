import krylov.Convergence.OneGradientCubicMetric
import krylov.OneGradient.CompletionCG
import krylov.Reference.EnergyPositive

/-!
Article: main_krylov, thm:LB, genuine last-normal error normalization.
Use: identify the hidden minimizer coordinate with the actual last CG
energy error and true inverse-root normal length. All quantities come
from the positive full-atom quadratic and its executed CG reference.
Source: true CG termination, exact last Lanczos residual and the actual
inverse-pivot/step-length identity, proved earlier for the whole fibre.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Envelope krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The literal minimizer of the true positive reference quadratic.
Article: main_krylov, thm:LB. -/
def oneGradientQuadraticMinimizer (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (g : E) : E :=
  -(cgOperator A⁻¹ g)

/-- The actual inverse constructs a genuine quadratic critical point.
Article: thm:LB. -/
theorem oneGradientQuadraticMinimizer_critical
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) :
    g+cgOperator A (oneGradientQuadraticMinimizer A g)=0 := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hi : cgOperator A (cgOperator A⁻¹ g)=g := by
    have hh := congrArg (fun B=>cgOperator B g) (Matrix.mul_nonsing_inv A hd)
    simpa only [cgOperator,map_mul,mul_apply_eq_comp,map_one,one_apply_eq_self] using hh
  rw [oneGradientQuadraticMinimizer,map_neg,hi,add_neg_cancel]

/-- Full actual CG ends at the real quadratic minimizer, independently
of the policy used in the adversarial argument. Article: thm:LB. -/
theorem oneGradientQuadraticMinimizer_eq_final_displacement
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E)
    (hc : referenceAtomCount A hA g=k+1) :
    oneGradientQuadraticMinimizer A g=CG.displacement (cgOperator A) g (k+1) := by
  have hh := CG.gradient_displacement (cgOperator A) g (k+1)
  have ht : CG.gradient (cgOperator A) g (k+1)=0 := by
    simpa only [hc] using cg_terminates A hA g
  rw [ht] at hh
  have hcrit := oneGradientQuadraticMinimizer_critical A hA g
  have hzero : cgOperator A (oneGradientQuadraticMinimizer A g-CG.displacement (cgOperator A) g (k+1))=0 := by
    rw [map_sub]
    rw [eq_neg_of_add_eq_zero_right hcrit,eq_neg_of_add_eq_zero_right hh.symm]
    exact sub_self _
  apply sub_eq_zero.mp
  by_contra hne
  have hp := (cgOperator_positive A hA).2 _ hne
  rw [hzero,inner_zero_right] at hp
  exact (lt_irrefl 0) hp

/-- The actual old CG displacement has zero hidden last-normal
coordinate, as required by the original cubic fibre. Article: thm:LB. -/
theorem oneGradient_last_old_coordinate_zero
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) :
    inner ℝ (lastLanczosVector A hA g hg hc) (CG.displacement (cgOperator A) g k)=0 := by
  rw [CG.displacement,inner_sum]
  apply sum_eq_zero
  intro i hi
  have hil := mem_range.mp hi
  rw [inner_smul_right]
  have hmem : CG.direction (cgOperator A) g i∈CG.krylovSpace (cgOperator A) g k := by
    apply krylovSpace_mono _ _ (show i+1≤k by omega)
    exact cgDirection_mem_krylov _ _ i (fun j hj=>(cgLength_pos A hA g j (by rw [full_gradient_atom_count A hA g hc];omega)).ne')
  rw [(krylov_last_lanczos_hyperplane A hA g hg hc _).mp hmem,mul_zero]

/-- The hidden minimizer coordinate is exactly the common last residual
normal coefficient times the genuine inverse pivot. Article: thm:LB. -/
theorem oneGradient_last_minimizer_coordinate
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) :
    inner ℝ (lastLanczosVector A hA g hg hc) (oneGradientQuadraticMinimizer A g)=
      -CG.length (cgOperator A) g k*inner ℝ (lastLanczosVector A hA g hg hc) (CG.gradient (cgOperator A) g k) := by
  rw [oneGradientQuadraticMinimizer_eq_final_displacement A hA g (full_gradient_atom_count A hA g hc),
    CG.displacement_succ,inner_add_right,oneGradient_last_old_coordinate_zero A hA g hg hc,
    inner_smul_right,last_cg_normal_direction A hA g hg hc]
  ring

/-- Exact true inverse-root hidden-normal energy equals the genuine last
CG length. Article: main_krylov, thm:LB, C_z²=alpha_(n-1). -/
theorem oneGradient_last_dual_norm_sq
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) :
    ‖cgOperator (metricRoot A)⁻¹ (lastLanczosVector A hA g hg hc)‖^2=CG.length (cgOperator A) g k := by
  rw [←last_inverse_pivot_cg_length A hA g hg hc]
  exact inverseRoot_energy A hA (WithLp.ofLp (lastLanczosVector A hA g hg hc))

/-- The original hidden-coordinate target is precisely the real last
reference CG energy error. No independently supplied reference error
normalization is assumed. Article: main_krylov, thm:LB. -/
theorem oneGradient_last_coordinate_energy
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) :
    (inner ℝ (lastLanczosVector A hA g hg hc) (oneGradientQuadraticMinimizer A g))^2=
      ‖cgOperator (metricRoot A)⁻¹ (lastLanczosVector A hA g hg hc)‖^2*‖cgCanonicalError A g k‖^2 := by
  let a := lastLanczosVector A hA g hg hc
  let γ := inner ℝ a (CG.gradient (cgOperator A) g k)
  have hgN := (last_cg_gradient_normal A hA g hg hc).1
  have he : ‖cgCanonicalError A g k‖^2=γ^2*‖cgOperator (metricRoot A)⁻¹ a‖^2 := by
    change ‖cgOperator (metricRoot A)⁻¹ (CG.gradient (cgOperator A) g k)‖^2=_
    rw [hgN,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [oneGradient_last_minimizer_coordinate A hA g hg hc,he,oneGradient_last_dual_norm_sq A hA g hg hc]
  change (-CG.length (cgOperator A) g k*γ)^2=CG.length (cgOperator A) g k*(γ^2*CG.length (cgOperator A) g k)
  ring

end
end krylov.Convergence
