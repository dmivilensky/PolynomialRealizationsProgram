import krylov.Functions.ReferencePlaneSource
import krylov.Functions.ScalarProbedExecution

/-!
Article: main_krylov, prop:Fcycle(iii), actual full reference search stationarity.
Use: derive the true scalar stationary endpoint on every actual reference
search, including the nonquadratic final gradient. Source: actual canonical
CG orthogonality and the exact first-direction terminal cubic gradient.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Methods
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual full complement reconstructs precisely the genuine terminal
CG reference point. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneTerminal_eq_node (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) :
    hilbertPlaneTerminal (referencePlaneFirst A g) (referencePlaneLast A hA g)
      (referencePlaneComplement A hA g) ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g)=
      referencePlaneNode A g (referenceAtomCount A hA g) := by
  dsimp only [hilbertPlaneTerminal,referencePlaneComplement]
  abel

/-- The genuine reference root is self-adjoint in every ambient dimension.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlane_metric_symmetric (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (metricCoordinates A hA).toContinuousLinearMap.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (krylov.Secant.metricRoot_isSymm A))

/-- Every actual scalar cubic reference endpoint is genuinely stationary
along its original physical CG search direction, through the last step.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneCubic_search_stationary (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (i : ℕ) (hi : i<referenceAtomCount A hA g)
    (d : EuclideanSpace ℝ (Fin n)) (α : ℝ) (hα : α≠0)
    (hstep : α • d=referenceStep (cgOperator A) g i) :
    inner ℝ (gradient
      (hilbertPlaneObjective (referencePlaneFirst A g) (referencePlaneLast A hA g)
        (referencePlaneComplement A hA g) ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t)
      (referencePlaneNode A g (i+1))) (metricCoordinates A hA d)=0 := by
  let S := metricCoordinates A hA
  let N := referenceAtomCount A hA g
  let F := hilbertPlaneObjective (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (referencePlaneComplement A hA g) ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t
  have hs : α • S d=canonicalCGStep A g i := by
    rw [←map_smul,hstep]
    change S (CG.length (cgOperator A) g i • CG.direction (cgOperator A) g i)=_
    rw [map_smul]
    rw [canonicalCGStep,cgStep,map_smul]
    rfl
  have hp : inner ℝ (gradient F (referencePlaneNode A g (i+1))) (canonicalCGStep A g i)=0 := by
    by_cases hinext : i+1<N
    · have hg := congrArg S.symm (referencePlaneCubicGradient_prefix A hA g hN t (i+1) hinext)
      change S.symm (gradient (metricHilbertPlaneObjective S _ _ _ _ _ t) _) =_ at hg
      rw [metricHilbertPlaneGradient_normalized S (referencePlane_metric_symmetric A hA),←referencePlaneNode_metric] at hg
      change gradient F (referencePlaneNode A g (i+1))=cgCanonicalError A g (i+1) at hg
      rw [hg,real_inner_comm]
      exact canonicalCGStep_postsearch_orth A hA g i
    · have hiN : i+1=N := by omega
      obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
      change ‖referencePlaneFirst A g‖=1 at he
      change ‖referencePlaneLast A hA g‖=1 at hh
      change inner ℝ (referencePlaneFirst A g) (referencePlaneLast A hA g)=0 at heh
      have hg := hilbertPlaneGradient_terminal (referencePlaneFirst A g) (referencePlaneLast A hA g)
        (referencePlaneComplement A hA g) he hh heh (referencePlaneComplement_project A hA g hN)
        ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t
      rw [referencePlaneTerminal_eq_node] at hg
      change gradient F (referencePlaneNode A g N)=_ at hg
      rw [hiN,hg,real_inner_smul_left]
      have hp0 := canonical_step_unit_pair A hA g (⟨0,by omega⟩) (⟨i,hi⟩)
      have hne : (⟨0,by omega⟩ : Fin N)≠⟨i,hi⟩ := by
        intro hh
        have hv := congrArg Fin.val hh
        change 0=i at hv
        omega
      have hz : inner ℝ (referencePlaneFirst A g) (canonicalCGStep A g i)=0 := by
        simpa only [referencePlaneFirst,ite_eq_right hne] using hp0
      rw [hz,mul_zero]
  have hz : α*inner ℝ (gradient F (referencePlaneNode A g (i+1))) (S d)=0 := by
    rw [←inner_smul_right,hs,hp]
  exact (mul_eq_zero.mp hz).resolve_left hα

/-- The real quadratic line step of every original globally consistent
policy is its genuine CG step, without any supplied direction scale.
Article: main_krylov, prop:Fcycle(iii). -/
theorem scalar_quadratic_line_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ProbedMethod E) (hm : CGConsistent m) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (i : ℕ) :
    let H := methodRun m (fun _=>Q) (fun _=>Q) g i
    lineLength H.gradient (m.direction H) (Q (m.direction H)) • m.direction H=referenceStep Q g i := by
  obtain ⟨c,hc,hd,_⟩ := hm Q hQ hpos g i
  dsimp only
  rw [hd,map_smul,quadratic_gradient_eq_cg m hm Q hQ hpos g i,lineStep_smul _ _ _ hc.ne']
  rfl

end
end krylov.Functions
