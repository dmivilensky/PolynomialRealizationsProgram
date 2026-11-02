import jacobi.Analytic.ReferenceComplexBeta

/-!
Article: jacobi, Appendix E.1.
The complete complex reference theory uses the original convergent
sine integral and the same actual Gauss energy function. This entry
also writes joint holomorphy and endpoint continuity literally in the
article's exponent gamma and squared frequency, through their exact
polynomial change from the already proved complex order and energy.
Use: completes the exact parameter formulation of fboundC(a), including zero frequency, for the same function represented by the genuine complex sine integral.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set
set_option backward.isDefEq.respectTransparency false

/-- The original reference solution is jointly holomorphic in the literal article parameters gamma and omega squared throughout Re(gamma)>0.
Use: completes the exact parameter formulation of fboundC(a), including zero frequency, for the same function represented by the genuine complex sine integral.
Article: jacobi, Lemma C.1.
Proof: the original affine order is alpha=2*gamma-3/2 and the energy is c_0alpha+omega squared. This polynomial map is jointly complex differentiable and maps into the proved admissible domain. Compose it with the full Frechet derivative of the actual reference solution. -/
theorem reference_joint_squared_frequency {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) :
    DifferentiableOn ℂ (fun p:ℂ × ℂ =>
      solution (2*p.1-3/2) (jacobi.Hankel.besselCoefficient (2*p.1-3/2)+p.2) t)
      {p | 0<p.1.re} := by
  -- The polynomial energy shift preserves the full two-dimensional derivative, including its frequency branch point.
  intro p hp
  have hg : gamma (2*p.1-3/2)=p.1 := by unfold gamma; ring
  have hU : IsOpen {q:ℂ × ℂ | 0<(gamma q.1).re} := by
    apply isOpen_lt continuous_const
    unfold gamma
    fun_prop
  have hbase := (solution_joint_holomorphic ht).differentiableAt
    (x := (2*p.1-3/2,jacobi.Hankel.besselCoefficient (2*p.1-3/2)+p.2))
    (hU.mem_nhds (by simpa only [mem_ofPred_eq,hg] using hp))
  have hP : DifferentiableAt ℂ (fun q:ℂ × ℂ =>
      (2*q.1-3/2,jacobi.Hankel.besselCoefficient (2*q.1-3/2)+q.2)) p := by
    unfold jacobi.Hankel.besselCoefficient
    fun_prop
  exact (hbase.comp p hP).differentiableWithinAt

/-- The actual original reference solution is jointly continuous in physical position, gamma and omega squared, including the zero endpoint.
Use: completes the closed-half-interval continuity assertion of fboundC(a) in precisely the printed parameters.
Article: jacobi, Lemma C.1.
Proof: the genuine original energy series and sine power are jointly continuous, including the singular physical endpoint. Compose their proved joint continuity with the exact affine order and polynomial energy change. -/
theorem reference_joint_squared_frequency_continuous {g lambda:ℂ} (hg:0<g.re)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    ContinuousAt (fun p:ℝ × ℂ × ℂ => solution (2*p.2.1-3/2)
      (jacobi.Hankel.besselCoefficient (2*p.2.1-3/2)+p.2.2) p.1) (t,g,lambda) := by
  -- Continuity uses the same literal energy shift as joint holomorphy and retains the true zero endpoint.
  have hgg : gamma (2*g-3/2)=g := by unfold gamma; ring
  have ha : 0<(gamma (2*g-3/2)).re := by rw [hgg]; exact hg
  have hc := solution_joint_continuous (a := 2*g-3/2)
    (z := jacobi.Hankel.besselCoefficient (2*g-3/2)+lambda) ha ⟨ht.1,by linarith [ht.2]⟩
  have hmap : Continuous (fun p:ℝ × ℂ × ℂ =>
      (2*p.2.1-3/2,jacobi.Hankel.besselCoefficient (2*p.2.1-3/2)+p.2.2,p.1)) := by
    unfold jacobi.Hankel.besselCoefficient
    fun_prop
  exact hc.comp (x := (t,g,lambda)) hmap.continuousAt

end
end jacobi.ComplexReference
