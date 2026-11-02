import krylov.Convergence.RFCPathRate
import krylov.Convergence.WindowRateShift

/-!
Article: main_krylov, thm:Ip, exact physical RFC gradient clock.
Use: enumerate every actual accepted and probe point after the genuine
seed, retaining the original two-gradient cost. Source: the true bounded
probe and the established integral R-order clock theorem.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Literal accepted and evaluated-probe query points, in observed order. -/
def rfcPathGradientQuery {E : Type*} [Add E] (x v : ℕ → E) (j : ℕ) : E :=
  let k:=j/2
  if j%2=0 then x (k+n+1) else x (k+n+1)+v k

/-- The literal accepted and evaluated-probe queries have precisely the
printed tau_1(dimension)^(1/2) order per evaluated gradient. -/
theorem rfcPath_gradient_query_rorder
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    (S : Set (EuclideanSpace ℝ (Fin (n+2)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+2)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (x v : ℕ → EuclideanSpace ℝ (Fin (n+2)))
    {γ : ℝ} (hγ : 0<γ)
    (hquery : ∀ k,x (k+n+2)=evaluatedRFCPoint G (windowStep (n:=n+1) x k)
      (windowImage G x k) (x (k+n+1)) (v k) γ)
    (hconv : Tendsto x atTop (𝓝 0))
    (hsolve : ∀ᶠ k in atTop,IsUnit (slidingRFCSolveMatrix (n:=n) G x k).det)
    (hconj : ∀ᶠ k in atTop,∀ i : Fin (n+1),inner ℝ (windowImage G x k i) (v k)=0)
    {cP : ℝ} (hprobe : ∀ᶠ k in atTop,
      v k≠0 ∧
      ‖v k‖≤
        cP*‖x (k+n+1)‖)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1)
    (hgain : ∀ᶠ k in atTop,∀ c : Fin (n+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (n:=n+1) (x) k)) c‖^2) :
    HasROrder (fun j=>‖rfcPathGradientQuery (n:=n) x v j‖)
      ((oneGradientRoot (n+2))^(1/2:ℝ)) := by
  have hrate := rfcPath_rorder G H S hS h₀ hnbhd hH hH₀ hG hG₀
    x v hγ hquery hconv hsolve hconj hprobe hσ hσ₁ hgain
  have hτ : 1<oneGradientRoot (n+2) := secantRoot_gt_one _ _
  have hshift := hrate.shift (zero_lt_one.trans hτ) (n+1)
  have hclock := hshift.clock hτ 2 (by norm_num)
  have hlim : Tendsto (fun j : ℕ=>j/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (2*b)] with j hj
    omega
  have hbounds : ∀ᶠ j in atTop,‖rfcPathGradientQuery (n:=n) x v j‖≤
      (1+|cP|)*‖x (j/2+(n+1))‖ := by
    filter_upwards [hlim.eventually hprobe] with j hj
    dsimp only [rfcPathGradientQuery]
    split_ifs
    · exact le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg cP])
    · have hh := (norm_add_le (x (j/2+n+1)) (v (j/2))).trans (add_le_add le_rfl
        (hj.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))))
      simpa only [Nat.add_assoc,add_mul,one_mul] using hh
  have hh := hclock.eventually_mono (by positivity : (0:ℝ)<1+|cP|) hbounds
  simpa only [Nat.cast_ofNat,one_div] using hh

end
end krylov.Convergence
