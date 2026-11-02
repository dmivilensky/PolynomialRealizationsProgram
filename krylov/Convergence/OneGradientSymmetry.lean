import krylov.Convergence.OneGradientSourceBounds

/-!
Article: main_krylov, thm:V and prop:EL, true scalar source symmetry.
Use: derive genuine symmetry of all actual evaluated and semantic output
Hessian averages from primitive scalar derivatives on their true local ball.
No symmetric source-operator field is postulated.
Source: Schwarz's theorem for actual second derivatives and the proved
Bochner average symmetry theorem.
-/
namespace krylov.Convergence
noncomputable section
open Set Filter Topology Metric krylov.Methods krylov.Functions chebyshev1.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Actual scalar-gradient derivatives give a symmetric true Hessian at
every point of the original open ball. Article: thm:Htransfer, thm:V. -/
theorem genuine_hessian_symmetric_ball
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ)
    (hF : ∀ x∈ball 0 r,HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x) (z : E) (hz : z∈ball 0 r) :
    (H z).toLinearMap.IsSymmetric := by
  have hnb : ∀ᶠ y in 𝓝 z,y∈ball 0 r := isOpen_ball.mem_nhds hz
  have he : ∀ᶠ y in 𝓝 z,HasFDerivAt f (innerSL ℝ (G y)) y := hnb.mono (fun y hy=>hF y hy)
  have hd : HasFDerivAt (fun y=>innerSL ℝ (G y)) ((innerSL ℝ).comp (H z)) z :=
    (innerSL ℝ).hasFDerivAt.comp z (hG z hz)
  intro a b
  have hs := second_derivative_symmetric_of_eventually he hd a b
  exact hs.trans (real_inner_comm _ _)

/-- The real scalar secant average on any enclosed chord is symmetric,
including zero steps. Article: lem:cycle-transfer, thm:V and prop:EL. -/
theorem genuine_secant_symmetric_ball
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ)
    (hH : ContinuousOn H (ball 0 r))
    (hF : ∀ x∈ball 0 r,HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (a b : E) (ha : a∈ball 0 r) (hb : b∈ball 0 r) :
    (averagedDerivative H a (b-a)).toLinearMap.IsSymmetric := by
  have hseg t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈ball 0 r := by
    apply (convex_ball (0:E) r).add_smul_mem ha _ ht
    simpa only [add_sub_cancel] using hb
  exact averagedDerivative_symmetric H a (b-a)
    (hH.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg)
    (fun t ht=>genuine_hessian_symmetric_ball f G H r hF hG _ (hseg t ht))

/-- Every true scalar one-gradient source operator is symmetric once its
actual query vertices and output have been enclosed. Article: thm:V. -/
theorem oneGradientFunction_operators_symmetric
    (m : OneGradientMethod E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (x₀ : E) (N : ℕ) (r : ℝ) (hH : ContinuousOn H (ball 0 r))
    (hF : ∀ x∈ball 0 r,HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x)
    (hp : ∀ i≤N,oneGradientFunctionPoint m G x₀ i∈ball 0 r)
    (ho : oneGradientFunctionOutput m G x₀ N∈ball 0 r) :
    (∀ i<N,(oneGradientFunctionOperator m G H x₀ i).toLinearMap.IsSymmetric) ∧
      (oneGradientFunctionOutputOperator m G H x₀ N).toLinearMap.IsSymmetric := by
  constructor
  · intro i hi
    rw [oneGradientFunctionOperator,oneGradientFunctionStep_eq_difference]
    exact genuine_secant_symmetric_ball f G H r hH hF hG _ _ (hp i hi.le) (hp (i+1) (by omega))
  · have hs : m.output (oneGradientFunctionRun m G x₀ N)=
        oneGradientFunctionOutput m G x₀ N-oneGradientFunctionPoint m G x₀ N := by
      rw [oneGradientFunctionOutput,add_sub_cancel_left]
    rw [oneGradientFunctionOutputOperator,hs]
    exact genuine_secant_symmetric_ball f G H r hH hF hG _ _ (hp N le_rfl) ho

end
end krylov.Convergence
