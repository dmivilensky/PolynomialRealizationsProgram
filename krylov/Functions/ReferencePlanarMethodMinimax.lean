import krylov.Functions.PlanarOriginalMethodMinimax
import krylov.Functions.ReferencePlaneInitialRadius
import krylov.Functions.ReferencePlaneCoefficient

/-!
Article: main_krylov, thm:Fplanar, actual-reference minimax normalization.
Use: discharge the original unknown-base interval from true reference CG
geometry, substitute the known tensor budget 2(1-delta), and identify the
actual full-reference sharp coefficient in the original method infimum.
Source: genuine first/last projection, true CG energy identities and the
complete original-base one-correction planar minimax theorem.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference krylov.Tensor.BinaryCubic
open scoped InnerProductSpace ENNReal Matrix.Norms.L2Operator
variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- The full original method minimax has the printed actual CG coefficient.
Its independent base interval is exactly the original initial-error bound;
admissibility of both information witnesses follows from true CG geometry,
rather than an enlarged source interval. The endpoint-only centre attains
the upper side with a uniform fourth-order loss.
Article: main_krylov, thm:Fplanar, full reference and original beta scope. -/
theorem referencePlanarMethodMinimax_bounds
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (a : ℝ) (ha : 0<a) (ha₁ : a≤1) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ H : History Plane,
      let p := ε*‖canonicalCGStep A g 0‖
      let r := referencePlaneRatio A hA g
      let L := ‖cgCanonicalError A g 0‖/‖canonicalCGStep A g 0‖
      let K := a^2*referenceFibreCoefficient A g (referenceAtomCount A hA g-1)
      ENNReal.ofReal (K*ε^3-C*ε^4)≤planeOriginalMethodMinimax (2*a) r p L H ∧
      planeOriginalMethodMinimax (2*a) r p L H≤
        planeOriginalMethodWorst (2*a) r p L H
          (budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) (2*a) (by decide)) ∧
      planeOriginalMethodWorst (2*a) r p L H
          (budgetedCentreValueMethod (ContinuousLinearEquiv.refl ℝ Plane) (2*a) (by decide))≤
        ENNReal.ofReal (K*ε^3+C*ε^4) := by
  let p₀ := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  let L := ‖cgCanonicalError A g 0‖/p₀
  obtain ⟨hp₀,hv,_,_,_,_,_⟩ := referencePlane_sample_lines A hA g hN
  change 0<p₀ at hp₀
  have hr : 0<r := hv
  have hL : (2*a)/2*Real.sqrt (1+r^2)≤L := by
    apply (le_div_iff₀ hp₀).mpr
    have hh := referencePlane_initial_radius A hA g hN
    have ha' := mul_le_mul_of_nonneg_right ha₁ (Real.sqrt_nonneg (1+r^2))
    have hm := mul_le_mul_of_nonneg_right ha' hp₀.le
    change p₀*Real.sqrt (1+r^2)≤‖cgCanonicalError A g 0‖ at hh
    nlinarith only [hm,hh]
  obtain ⟨C,hC,hbound⟩ := planeOriginalMethodMinimax_bounds (2*a) r L (by positivity) hr hL
  let ep := 1/(2*a*p₀+1)
  refine ⟨ep,C*p₀^4,by dsimp only [ep]; positivity,mul_pos hC (pow_pos hp₀ _),?_⟩
  intro ε hε he H
  dsimp only
  have hp : 0<ε*p₀ := mul_pos hε hp₀
  have hp₁ : 2*a*(ε*p₀)≤1 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*a*p₀+1)).mp he
    nlinarith only [hh,hε]
  have hb := hbound (ε*p₀) hp hp₁ H
  have hcoef := referencePlane_coefficient A hA g hN
  change r^2*Real.sqrt (1+4*r^2)*fibreMinimax r*p₀^3=
    referenceFibreCoefficient A g (referenceAtomCount A hA g-1) at hcoef
  have heq : (2*a)^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*(ε*p₀)^3=
      a^2*referenceFibreCoefficient A g (referenceAtomCount A hA g-1)*ε^3 := by
    rw [←hcoef]
    ring
  have herr : C*(ε*p₀)^4=(C*p₀^4)*ε^4 := by ring
  rw [heq,herr] at hb
  exact hb

end
end krylov.Functions
