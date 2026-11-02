import krylov.Convergence.OneGradientJacobiSource
import krylov.OneGradient.XRFCTwoBasisOutput
import krylov.Methods.Classes

/-!
Article: main_krylov, thm:LB, genuine cubic attainment in both XRFC bases.
Use: identify the actual function output on the original indistinguishable
rank-one cubic family, rather than only its abstract tensor coefficient.
Source: exact actual transcript equality, true native quadratic termination
in both bases, and the genuine last-coordinate/CG-energy identity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Either actual XRFC basis returns the genuine quadratic minimizer.
Article: main_krylov, thm:LB, source family attainment. -/
theorem xrfcBasis_quadratic_minimizer
    (directions : Bool) (trial : History E → ℝ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E)
    (hfull : referenceAtomCount A hA g=k+1)
    (ht : ∀ i<k+1,trial (oneGradientRun (xrfcBasisMethod directions trial) (fun _=>cgOperator A) g i)≠0) :
    (xrfcBasisMethod directions trial).outputDisplacement
      (oneGradientRun (xrfcBasisMethod directions trial) (fun _=>cgOperator A) g (k+1))=
      oneGradientQuadraticMinimizer A g := by
  rw [oneGradientQuadraticMinimizer_eq_final_displacement A hA g hfull]
  cases directions with
  | false =>
    change (xrfcMethod fullMemory trial).outputDisplacement _=_
    have hh := (xrfc_full_terminates A hA g trial (fun i hi=>ht i (by simpa only [hfull] using hi))).1
    simpa only [hfull,xrfcBasisMethod,ite_false,Bool.false_eq_true] using hh
  | true =>
    change (xrfcDMethod fullMemory trial).outputDisplacement _=_
    have hh := (xrfcD_terminates A hA g fullMemory trial (fun _ _ hi=>hi)
      (fun i hi=>ht i (by simpa only [hfull] using hi))).1
    simpa only [hfull,xrfcBasisMethod,ite_true] using hh

/-- The real last query in either XRFC basis has the true last-line
hidden-coordinate ratio tau/alpha. Article: main_krylov, thm:LB. -/
theorem xrfcBasis_last_query_coordinate
    (directions : Bool) (trial : History E → ℝ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g a : E)
    (hfull : referenceAtomCount A hA g=k+1)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0)
    (ht : ∀ i<k+1,trial (oneGradientRun (xrfcBasisMethod directions trial) (fun _=>cgOperator A) g i)≠0) :
    inner ℝ a (oneGradientLastQuery (xrfcBasisMethod directions trial) (cgOperator A) g k)=
      (trial (oneGradientRun (xrfcBasisMethod directions trial) (fun _=>cgOperator A) g k)/CG.length (cgOperator A) g k)*
        inner ℝ a (oneGradientQuadraticMinimizer A g) := by
  let method:=xrfcBasisMethod directions trial
  have hpre i (hi : i<k+1) := cg_nonstagnation A hA g i (by rw [hfull];exact hi)
  have heval : oneGradientLastQuery method (cgOperator A) g k=CG.displacement (cgOperator A) g k+
      trial (oneGradientRun method (fun _=>cgOperator A) g k) • CG.direction (cgOperator A) g k := by
    have he : oneGradientLastQuery method (cgOperator A) g k=
        (oneGradientRun method (fun _=>cgOperator A) g (k+1)).displacement := by
      change (oneGradientRun method (fun _=>cgOperator A) g k).displacement+
        method.step (oneGradientRun method (fun _=>cgOperator A) g k)=_
      exact add_comm _ _
    rw [he]
    cases directions with
    | false =>
      exact xrfc_full_evaluated trial _ (cgOperator_positive A hA).1
        (cgOperator_positive A hA).2 g (k+1) hpre ht k (by omega)
    | true =>
      exact xrfcD_evaluated fullMemory trial _ (cgOperator_positive A hA).1
        (cgOperator_positive A hA).2 g (k+1) hpre (fun _ _ hi=>hi) ht k (by omega)
  have hy : inner ℝ a (oneGradientQuadraticMinimizer A g)=
      CG.length (cgOperator A) g k*inner ℝ a (CG.direction (cgOperator A) g k) := by
    rw [oneGradientQuadraticMinimizer_eq_final_displacement A hA g hfull,CG.displacement_succ,
      inner_add_right,oneGradient_normal_old_coordinate A hA g a hfull hflag,inner_smul_right,zero_add]
  rw [heval,inner_add_right,oneGradient_normal_old_coordinate A hA g a hfull hflag,inner_smul_right,zero_add,hy]
  have hα : CG.length (cgOperator A) g k≠0 := (cgLength_pos A hA g k (by rw [hfull];omega)).ne'
  field_simp
  dsimp only [method]
  ring

/-- Exact actual-function attainment on the genuine cubic twins in both
original bases. The displayed value is exact in the endpoint metric;
true-minimizer metric replacement is handled by the proved uniform
relative neighborhoods. No scalar-source output is assumed.
Article: main_krylov, thm:LB, rank-one cubic attainment. -/
theorem xrfcBasis_cubic_actual_attainment
    (directions : Bool) (trial : History E → ℝ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g a : E) (ha : ‖a‖=1)
    (hfull : referenceAtomCount A hA g=k+1)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0)
    (ht : ∀ i<k+1,trial (oneGradientRun (xrfcBasisMethod directions trial) (fun _=>cgOperator A) g i)≠0)
    (t : ℝ) :
    let method:=xrfcBasisMethod directions trial
    let p:=inner ℝ a (oneGradientLastQuery method (cgOperator A) g k)
    let G:=oneGradientCubicFibreGradient (cgOperator A) g a (-t*p/2) t
    oneGradientFunctionOutput method G 0 (k+1)=oneGradientQuadraticMinimizer A g ∧
      ‖cgOperator (metricRoot A)⁻¹ (G (oneGradientFunctionOutput method G 0 (k+1)))‖=
        |t|/2*‖cgOperator (metricRoot A)⁻¹ a‖^3*
          |1-trial (oneGradientRun method (fun _=>cgOperator A) g k)/CG.length (cgOperator A) g k| *
          ‖cgCanonicalError A g k‖^2 := by
  let method:=xrfcBasisMethod directions trial
  let p:=inner ℝ a (oneGradientLastQuery method (cgOperator A) g k)
  let G:=oneGradientCubicFibreGradient (cgOperator A) g a (-t*p/2) t
  let y:=inner ℝ a (oneGradientQuadraticMinimizer A g)
  let c:=‖cgOperator (metricRoot A)⁻¹ a‖
  have hmeth : OneGradientSpanRestricted method := by
    cases directions with
    | false => exact xrfcMethod_spanRestricted fullMemory trial
    | true => exact xrfcDMethod_spanRestricted fullMemory trial
  have houtput : oneGradientFunctionOutput method G 0 (k+1)=oneGradientQuadraticMinimizer A g := by
    have hh := oneGradientCubicTwins_output method hmeth (cgOperator A) g a t k
      (fun v hv=>(hflag v).mp hv) 1
    simp only [neg_one_mul,one_mul] at hh
    exact hh.trans (xrfcBasis_quadratic_minimizer directions trial A hA g hfull ht)
  refine ⟨houtput,?_⟩
  rw [houtput]
  have hgrad : G (oneGradientQuadraticMinimizer A g)=(t/2*y*(y-p)) • a := by
    dsimp only [G]
    rw [oneGradientCubicFibreGradient_eq,oneGradientQuadraticMinimizer_critical A hA g,zero_add]
    congr 1
    dsimp only [y]
    ring
  have hp : |y-p|=|1-trial (oneGradientRun method (fun _=>cgOperator A) g k)/CG.length (cgOperator A) g k| *|y| := by
    rw [show p= _ from xrfcBasis_last_query_coordinate directions trial A hA g a hfull hflag ht]
    change |y- _*y|=_
    rw [show y- _*y=(1-trial (oneGradientRun method (fun _=>cgOperator A) g k)/CG.length (cgOperator A) g k)*y by ring,abs_mul]
  have henergy := oneGradient_normal_coordinate_energy A hA g a ha hfull hflag
  change y^2=c^2*‖cgCanonicalError A g k‖^2 at henergy
  change ‖cgOperator (metricRoot A)⁻¹ (G (oneGradientQuadraticMinimizer A g))‖=_
  rw [hgrad,map_smul,norm_smul,Real.norm_eq_abs,abs_mul,abs_mul,abs_div,
    abs_of_nonneg (by norm_num : (0:ℝ)≤2),hp]
  change _*c=_
  calc
    _ = |t|/2*c*|1-trial (oneGradientRun method (fun _=>cgOperator A) g k)/CG.length (cgOperator A) g k| *|y|^2 := by ring
    _ = _ := by
      rw [sq_abs,henergy]
      dsimp only [c,method]
      ring

end
end krylov.Convergence
