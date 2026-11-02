import krylov.Convergence.OneGradientFibreQuery

/-!
Article: main_krylov, thm:LB, fixed normalized information geometry.
Use: retain one genuine hidden unit normal while the forcing is scaled
and the last pivot varies. Only its actual Krylov hyperplane is used;
no orientation/scaling convention for a freshly recomputed Lanczos basis
is imposed. Source: real power-space scaling, true CG Galerkin
orthogonality and exact quadratic metric duality.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Nonzero scalar forcing changes no actual Krylov information space.
Article: main_krylov, thm:LB, fixed normalized information. -/
theorem oneGradient_krylovSpace_smul
    (Q : E →L[ℝ] E) (g : E) (h : ℝ) (hh : h≠0) (N : ℕ) :
    CG.krylovSpace Q (h • g) N=CG.krylovSpace Q g N := by
  rw [krylov_space_powers,krylov_space_powers]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change (Q^i) (h • g)∈_
    rw [map_smul]
    exact Submodule.smul_mem _ h (Submodule.subset_span ⟨i,hi,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    have he : (Q^i) g=h⁻¹ • ((Q^i) (h • g)) := by
      rw [map_smul,smul_smul,inv_mul_cancel₀ hh,one_smul]
    change (Q^i) g∈_
    rw [he]
    exact Submodule.smul_mem _ h⁻¹ (Submodule.subset_span ⟨i,hi,rfl⟩)

/-- The actual penultimate CG residual is parallel to every genuine unit
normal of its known Krylov hyperplane. Article: thm:LB. -/
theorem oneGradient_terminal_normal_residual
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g a : E) (ha : ‖a‖=1)
    (hfull : referenceAtomCount A hA g=k+1)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0) :
    CG.gradient (cgOperator A) g k=(inner ℝ a (CG.gradient (cgOperator A) g k)) • a := by
  let r := CG.gradient (cgOperator A) g k
  let p := r-(inner ℝ a r) • a
  have haa : inner ℝ a a=1 := by rw [real_inner_self_eq_norm_sq,ha,one_pow]
  have hap : inner ℝ a p=0 := by
    dsimp only [p]
    rw [inner_sub_right,inner_smul_right,haa,mul_one,sub_self]
  have hpK : p∈CG.krylovSpace (cgOperator A) g k := (hflag p).mpr hap
  have hpr : inner ℝ p r=0 := CG.gradient_orthogonal_krylov (cgOperator A)
    (cgOperator_positive A hA).1 (cgOperator_positive A hA).2 g k
    (fun j hj=>cg_nonstagnation A hA g j (by rw [hfull];omega)) hpK
  have hpa : inner ℝ p a=0 := (real_inner_comm _ _).trans hap
  have hpp : inner ℝ p p=0 := by
    change inner ℝ p (r-(inner ℝ a r) • a)=0
    rw [inner_sub_right,inner_smul_right,hpr,hpa,mul_zero,sub_self]
  exact (sub_eq_zero.mp (inner_self_eq_zero.mp hpp)).symm.symm

/-- The actual old CG displacement lies in the true hidden hyperplane.
Article: main_krylov, thm:LB. -/
theorem oneGradient_normal_old_coordinate
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g a : E)
    (hfull : referenceAtomCount A hA g=k+1)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0) :
    inner ℝ a (CG.displacement (cgOperator A) g k)=0 := by
  rw [CG.displacement,inner_sum]
  apply sum_eq_zero
  intro i hi
  rw [inner_smul_right]
  have him : CG.direction (cgOperator A) g i∈CG.krylovSpace (cgOperator A) g k := by
    apply krylovSpace_mono _ _ (show i+1≤k by have hi:=mem_range.mp hi;omega)
    exact cgDirection_mem_krylov _ _ i (fun j hj=>(cgLength_pos A hA g j (by rw [hfull];have hi:=mem_range.mp hi;omega)).ne')
  rw [(hflag _).mp him,mul_zero]

/-- Exact last-coordinate/error identity for one fixed genuine hidden
axis, uniformly under arbitrary physical completions and nonzero forcing
scales that preserve its actual old hyperplane. Article: thm:LB. -/
theorem oneGradient_normal_coordinate_energy
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g a : E) (ha : ‖a‖=1)
    (hfull : referenceAtomCount A hA g=k+1)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0) :
    (inner ℝ a (oneGradientQuadraticMinimizer A g))^2=
      ‖cgOperator (metricRoot A)⁻¹ a‖^2*‖cgCanonicalError A g k‖^2 := by
  let x₀ := oneGradientQuadraticMinimizer A g
  let d := CG.displacement (cgOperator A) g k
  let γ := inner ℝ a (CG.gradient (cgOperator A) g k)
  let c := ‖cgOperator (metricRoot A)⁻¹ a‖
  have hgrad := oneGradient_terminal_normal_residual A hA g a ha hfull hflag
  have hcrit : cgOperator A x₀= -g := eq_neg_of_add_eq_zero_right (oneGradientQuadraticMinimizer_critical A hA g)
  have hres : cgOperator A (d-x₀)=CG.gradient (cgOperator A) g k := by
    rw [map_sub,hcrit,sub_neg_eq_add]
    exact (add_comm _ _).trans (CG.gradient_displacement _ _ _).symm
  have hcoord := oneGradient_hidden_metric_pairing A hA a (d-x₀)
  rw [inner_sub_right,oneGradient_normal_old_coordinate A hA g a hfull hflag,
    zero_sub,hres,hgrad,map_smul,inner_smul_right,real_inner_self_eq_norm_sq] at hcoord
  change -inner ℝ a x₀=γ*c^2 at hcoord
  have he : ‖cgCanonicalError A g k‖^2=γ^2*c^2 := by
    change ‖cgOperator (metricRoot A)⁻¹ (CG.gradient (cgOperator A) g k)‖^2=_
    rw [hgrad,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  change (inner ℝ a x₀)^2=c^2*‖cgCanonicalError A g k‖^2
  rw [he,show inner ℝ a x₀= -γ*c^2 by nlinarith only [hcoord]]
  ring

/-- The genuine hidden minimizer coordinate is proportional to the
actual last CG length for any fixed unit normal, with its sign retained.
Article: main_krylov, thm:LB, endpoint selection. -/
theorem oneGradient_normal_minimizer_coordinate
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g a : E) (ha : ‖a‖=1)
    (hfull : referenceAtomCount A hA g=k+1)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0) :
    inner ℝ a (oneGradientQuadraticMinimizer A g)=
      -CG.length (cgOperator A) g k*inner ℝ a (CG.gradient (cgOperator A) g k) := by
  let r := CG.gradient (cgOperator A) g k
  let d := CG.direction (cgOperator A) g k
  let γ := inner ℝ a r
  have hgrad := oneGradient_terminal_normal_residual A hA g a ha hfull hflag
  have hγ : γ≠0 := by
    intro hz
    have hr := cg_nonstagnation A hA g k (by rw [hfull];omega)
    rw [hgrad,show inner ℝ a (CG.gradient (cgOperator A) g k)=0 from hz,zero_smul] at hr
    exact hr rfl
  have hsearch := (CG.invariant (cgOperator A) (cgOperator_positive A hA).1
    (cgOperator_positive A hA).2 g k
    (fun j hj=>cg_nonstagnation A hA g j (by rw [hfull];omega))).search_pair
  rw [hgrad,inner_smul_right,norm_smul,Real.norm_eq_abs,ha,mul_one,sq_abs] at hsearch
  change γ*inner ℝ d a= -γ^2 at hsearch
  rw [real_inner_comm a d] at hsearch
  have had : inner ℝ a d= -γ := by
    apply mul_left_cancel₀ hγ
    nlinarith only [hsearch]
  rw [oneGradientQuadraticMinimizer_eq_final_displacement A hA g hfull,CG.displacement_succ,
    inner_add_right,oneGradient_normal_old_coordinate A hA g a hfull hflag,zero_add,inner_smul_right]
  change CG.length (cgOperator A) g k*inner ℝ a d= -CG.length (cgOperator A) g k*γ
  rw [had]
  ring

end
end krylov.Convergence
