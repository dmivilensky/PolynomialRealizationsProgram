import krylov.Convergence.OneGradientLocalization

/-!
Article: main_krylov, thm:V and prop:EL, genuine local smooth-function queries.
Use: derive the actual compact finite-query enclosure from the original
continuous Hessian at the true positive quadratic reference. All model-error
Lipschitz constants, global auxiliary oracles and their agreement with the
original function are constructed internally.
Source: the true derivative mean-value theorem and native oracle locality.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Primitive local smoothness supplies every actual query bound needed
by the original one-gradient transfer, before a source jet is substituted.
Article: main_krylov, thm:V and prop:EL. -/
theorem compact_oneGradient_C1_localization
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (hQ : IsSelfAdjoint Q)
    (K : Set E) (hK : IsCompact K)
    (hstep : ∀ g∈K,∀ i<N,ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>oneGradientStep m (fcFiniteOperatorPath Q N z.2) z.1 i) (g,0))
    (hout : ∀ g∈K,ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>m.output (oneGradientRun m (fcFiniteOperatorPath Q N z.2) z.1 N)) (g,0))
    (hhom : ∀ (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ),0<c →
      (∀ i<N,oneGradientStep m A (c • g) i=c • oneGradientStep m A g i) ∧
        m.output (oneGradientRun m A (c • g) N)=c • m.output (oneGradientRun m A g N))
    (G : E → E) (H : E → E →L[ℝ] E) (r R : ℝ) (hr : 0<r) (hR : 0<R)
    (hG₀ : G 0=0) (hH₀ : H 0=Q) (hH : ContinuousAt H 0)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x) :
    ∃ ep D : ℝ,0<ep ∧0<D ∧∀ ε : ℝ,0<ε → ε<ep →∀ u : E,‖u‖≤R →Q u∈K →
      (∀ i≤N,oneGradientFunctionPoint m G (ε • u) i∈ball 0 r ∧
        ‖oneGradientFunctionPoint m G (ε • u) i‖≤ε*D) ∧
      (oneGradientFunctionOutput m G (ε • u) N∈ball 0 r ∧
        ‖oneGradientFunctionOutput m G (ε • u) N‖≤ε*D) ∧
      (∀ i<N,‖m.step (oneGradientFunctionRun m G (ε • u) i)‖≤ε*D) ∧
        ‖m.output (oneGradientFunctionRun m G (ε • u) N)‖≤ε*D := by
  obtain ⟨δ,M,hδ,hM,hloc⟩ := compact_oneGradient_localization m Q hQ K hK hstep hout hhom
  let q := Real.sqrt n
  let η : ℝ≥0 := ⟨δ/((q+1)*(R+1)),by dsimp only [q]; positivity⟩
  have hη : 0<η := by change 0<δ/((q+1)*(R+1)); dsimp only [q]; positivity
  have hq : 0≤q := Real.sqrt_nonneg _
  have heq : (η:ℝ)*((q+1)*(R+1))=δ := div_mul_cancel₀ δ (by positivity)
  have hsqrt : ((NNReal.sqrt n*η:ℝ≥0):ℝ)=q*(η:ℝ) := by
    simp only [NNReal.coe_mul,Real.coe_sqrt,NNReal.coe_natCast,q]
  have hsmall : ((NNReal.sqrt n*η:ℝ≥0):ℝ)≤δ ∧
      ((NNReal.sqrt n*η:ℝ≥0):ℝ)*R≤δ := by
    rw [hsqrt]
    have hprod : 0≤q*(η:ℝ)*R := by positivity
    constructor
    · nlinarith [η.2]
    · nlinarith [η.2]
  have hder : ∀ᶠ x in 𝓝 (0:E),HasFDerivAt G (H x) x := by
    filter_upwards [ball_mem_nhds (0:E) hr] with x hx
    exact hG x hx
  obtain ⟨ρ₀,hρ₀,hlocal⟩ := exists_gradient_error_lipschitz_ball G H Q hH₀ hH hder η hη
  let ρ := min r ρ₀
  have hρ : 0<ρ := lt_min hr hρ₀
  obtain ⟨ep,hep,hbounds⟩ := hloc G hG₀ ρ R hρ hR η
    (hlocal.mono (ball_subset_ball (min_le_right r ρ₀))) hsmall.1 hsmall.2
  let D := R+(N+1:ℕ)*M
  have hD : 0<D := by dsimp only [D]; positivity
  have hMD : M≤D := by
    have hn : (1:ℝ)≤(N:ℝ)+1 := by
      linarith only [show (0:ℝ)≤(N:ℝ) from Nat.cast_nonneg N]
    dsimp only [D]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hn hM.le,hR.le]
  refine ⟨ep,D,hep,hD,?_⟩
  intro ε hε he u hu hKu
  obtain ⟨hp,ho,hs,houtb⟩ := hbounds ε hε he u hu hKu
  exact ⟨fun i hi=>⟨ball_subset_ball (min_le_left r ρ₀) (hp i hi).1,(hp i hi).2⟩,
    ⟨ball_subset_ball (min_le_left r ρ₀) ho.1,ho.2⟩,
    fun i hi=>(hs i hi).trans (mul_le_mul_of_nonneg_left hMD hε.le),
    houtb.trans (mul_le_mul_of_nonneg_left hMD hε.le)⟩

end
end krylov.Convergence
