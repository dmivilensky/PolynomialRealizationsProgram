import krylov.OneGradient.CompletionCG
import krylov.Reference.FullCycle
import krylov.Reference.Energy
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), genuine last-normal physical prior form.
Use: identify the actual known-base rank-one displacement in the true
perturbed-reference canonical last-CG direction, without a supplied axis.
Source: genuine full-atom CG termination and energy, exact physical
normal residual geometry and actual positive-root rank-one transport.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A physical rank-one form along a true penultimate residual normal
is exactly the last-CG-axis rank-one canonical form. Its true coefficient
is the physical scalar times the actual final CG length.
Use: the original known-prior attainer is a genuine physical last-Lanczos
base displacement, rather than a postulated canonical rank-one prior.
Article: main_krylov, thm:local(b), real last-normal prior alignment.
Proof: exact full-atom CG gives its true final canonical residual and step
norm. The physical unit-normal residual identity determines the true
inverse-root normal vector. Actual CG energy identifies its squared scalar
with the genuine final line length. Exact rank-one congruence finishes. -/
theorem canonical_last_normal_form
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount A hA g=n+1)
    (z : EuclideanSpace ℝ (Fin (n+1))) (hz : ‖z‖=1) (gamma delta : ℝ) (hgamma : gamma≠0)
    (hgrad : CG.gradient (cgOperator A) g n=gamma • z) :
    cgOperator (relativeOperator A (delta • vecMulVec (WithLp.ofLp z) (WithLp.ofLp z)))=
      (delta*CG.length (cgOperator A) g n) • InnerProductSpace.rankOne ℝ
        (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n) := by
  let h := canonicalCGUnitStep A g n
  let sigma := ‖canonicalCGStep A g n‖
  let alpha := CG.length (cgOperator A) g n
  let u := cgOperator (metricRoot A)⁻¹ z
  let k := gamma⁻¹*(-sigma)
  have ho := canonicalCG_frame_of_full_atoms A hA g hc
  have hh : ‖h‖=1 := ho.norm_eq_one (Fin.last n)
  have hlast : cgOperator (metricRoot A)⁻¹ (CG.gradient (cgOperator A) g n)= -sigma • h :=
    canonicalCG_last_gradient A hA g ho
  have hu : u=k • h := by
    rw [hgrad,map_smul] at hlast
    have he := congrArg (fun v => gamma⁻¹ • v) hlast
    simpa only [u,k,smul_smul,inv_mul_cancel₀ hgamma,one_smul] using he
  have henergy : sigma^2=alpha*gamma^2 := by
    have he := cgEnergy_eq_length_norm A hA g (k := n) (by rw [hc];omega)
    rw [cgEnergy_eq_norm_sq A hA,hgrad,norm_smul,hz,mul_one,Real.norm_eq_abs,sq_abs] at he
    exact he
  have hk : k^2=alpha := by
    dsimp only [k]
    field_simp
    nlinarith [henergy]
  have hform : cgOperator (relativeOperator A (delta • vecMulVec (WithLp.ofLp z) (WithLp.ofLp z)))=
      delta • InnerProductSpace.rankOne ℝ u u := by
    rw [relativeOperator_smul,relativeOperator,rankOne_inverse_congruence _ (metricRoot_isSymm A).inv]
    simp only [cgOperator,map_smul,toEuclideanCLM_rankOne]
    rfl
  rw [hform,hu]
  apply ContinuousLinearMap.ext
  intro v
  simp only [_root_.smul_apply,InnerProductSpace.rankOne_apply,real_inner_smul_left,smul_smul]
  change (delta*((k*inner ℝ h v)*k)) • h=(delta*alpha*inner ℝ h v) • h
  congr 1
  nlinarith [congrArg (fun x : ℝ => delta*inner ℝ h v*x) hk]

end
end krylov.OneGradient
