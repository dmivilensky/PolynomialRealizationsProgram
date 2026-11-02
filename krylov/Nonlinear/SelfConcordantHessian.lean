import krylov.Nonlinear.GradientLocal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.GCongr

/-!
Article: main_krylov, thm:RFCS and apG:sc(iii), local self-concordant Hessian constants.
Use: Derive an actual Hessian Lipschitz constant of the form 2+C R near a
canonically normalized minimizer from its genuine mixed self-concordance
differential inequality, rather than assuming a local Lipschitz constant.
Source: Nesterov18, Lemma 5.1.2, mixed self-concordant differential inequality;
mathlib's actual operator norm and convex derivative mean-value theorem.
The explicit large coefficient below is immaterial: its constant term 2 is
retained exactly, as required by the final last-probe error coefficient.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine mixed self-concordance differential inequality bounds the true Hessian derivative norm by twice the cube of a square-root Hessian norm bound.
Use: Convert the standard mixed differential condition into a real operator-norm estimate.
Article: main_krylov, thm:RFCS, actual self-concordant local Hessian control.
Source: Nesterov18, Lemma 5.1.2, genuine mixed self-concordance differential bound.
Proof: Bound each local Hessian norm by the supplied Euclidean norm bound, apply the actual mixed inequality to the operator output itself and cancel its nonzero norm; nested true operator-norm bounds give the full derivative estimate.
-/
theorem selfConcordant_mixed_derivative_norm_le (H : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E)
    (hsc : ∀ u v w : E, |inner ℝ v (D u w)|≤
      2*Real.sqrt (inner ℝ u (H u))*Real.sqrt (inner ℝ v (H v))*Real.sqrt (inner ℝ w (H w)))
    {t : ℝ} (ht : 0≤t) (hH : ‖H‖≤t^2) : ‖D‖≤2*t^3 := by
  have hs (v : E) : Real.sqrt (inner ℝ v (H v))≤t*‖v‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    calc
      inner ℝ v (H v) ≤ |inner ℝ v (H v)| := le_abs_self _
      _ ≤ ‖v‖*‖H v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖*(‖H‖*‖v‖) := mul_le_mul_of_nonneg_left (H.le_opNorm v) (norm_nonneg _)
      _ ≤ (t*‖v‖)^2 := by nlinarith [mul_le_mul_of_nonneg_right hH (sq_nonneg ‖v‖)]
  apply D.opNorm_le_bound (by positivity)
  intro u
  apply (D u).opNorm_le_bound (by positivity)
  intro w
  let v := D u w
  have hb : ‖v‖^2≤(2*t^3*‖u‖*‖w‖)*‖v‖ := by
    calc
      _ = |inner ℝ v (D u w)| := by rw [show D u w=v from rfl,real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)]
      _ ≤ 2*Real.sqrt (inner ℝ u (H u))*Real.sqrt (inner ℝ v (H v))*Real.sqrt (inner ℝ w (H w)) := hsc u v w
      _ ≤ 2*(t*‖u‖)*(t*‖v‖)*(t*‖w‖) := by gcongr <;> exact hs _
      _ = _ := by ring
  by_cases hv : ‖v‖=0
  · change ‖v‖≤_
    rw [hv]
    positivity
  · have hv' := (norm_nonneg v).lt_of_ne' hv
    exact (mul_le_mul_iff_right₀ hv').mp (by simpa only [pow_two,v,mul_comm] using hb)


/-- A genuinely differentiated canonically normalized Hessian obeying the standard mixed self-concordance inequality has local Lipschitz constant at most 2+10000R on all sufficiently small balls.
Use: Supply the actual leading constant 2 with a linear radius remainder for the nonlinear RFC-S last-probe comparison.
Article: main_krylov, thm:RFCS, actual self-concordant local Hessian control.
Source: Nesterov18, Lemma 5.1.2, genuine mixed self-concordance differential bound.
Proof: Continuity first gives a coarse true derivative bound and hence linear Hessian growth from its exact identity value. Insert that real growth back into the mixed differential inequality and apply the convex mean-value theorem on each smaller ball.
-/
theorem selfConcordant_mixed_local_hessian_lipschitz (H : E → E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E) (r₀ : ℝ) (hr₀ : 0<r₀)
    (h₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hD : ∀ x∈ball 0 r₀, HasFDerivAt H (D x) x)
    (hsc : ∀ x∈ball 0 r₀, ∀ u v w : E, |inner ℝ v (D x u w)|≤
      2*Real.sqrt (inner ℝ u (H x u))*Real.sqrt (inner ℝ v (H x v))*Real.sqrt (inner ℝ w (H x w))) :
    ∃ r : ℝ, 0<r ∧ r≤r₀ ∧ r≤1 ∧ ∀ R : ℝ, 0<R → R≤r →
      LipschitzOnWith (Real.toNNReal (2+10000*R)) H (ball 0 R) := by
  have hcont : ContinuousAt (fun x : E => ‖H x-ContinuousLinearMap.id ℝ E‖) 0 :=
    ((hD 0 (mem_ball_self hr₀)).continuousAt.sub continuousAt_const).norm
  have hzero : ‖H 0-ContinuousLinearMap.id ℝ E‖=0 := by rw [h₀,sub_self,norm_zero]
  have hlt : ‖H 0-ContinuousLinearMap.id ℝ E‖<(1 : ℝ) := by rw [hzero]; norm_num
  have he : ∀ᶠ x in 𝓝 (0 : E), ‖H x-ContinuousLinearMap.id ℝ E‖<1 :=
    hcont.eventually (gt_mem_nhds hlt)
  obtain ⟨r₁,hr₁,hnear⟩ := Metric.eventually_nhds_iff.mp he
  let ρ := min r₀ r₁
  have hρ : 0<ρ := lt_min hr₀ hr₁
  have hsub {x : E} (hx : x∈ball 0 ρ) : x∈ball 0 r₀ := ball_subset_ball (min_le_left _ _) hx
  have hnorm {x : E} (hx : x∈ball 0 ρ) : ‖H x‖≤2 := by
    have hn := (hnear (ball_subset_ball (min_le_right _ _) hx)).le
    calc
      _ ≤ ‖H x-ContinuousLinearMap.id ℝ E‖+‖ContinuousLinearMap.id ℝ E‖ := by
        simpa only [sub_add_cancel] using norm_add_le (H x-ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
      _ ≤ 2 := by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)]
  -- First obtain genuine coarse control; this step uses no assumed local Lipschitz constant.
  have hcoarse : LipschitzOnWith 16 H (ball 0 ρ) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx => (hD x (hsub hx)).hasFDerivWithinAt) _ (convex_ball 0 ρ)
    intro x hx
    have hb := selfConcordant_mixed_derivative_norm_le (H x) (D x) (hsc x (hsub hx))
      (by norm_num : (0 : ℝ)≤2) (by linarith [hnorm hx] : ‖H x‖≤(2 : ℝ)^2)
    norm_num at hb
    exact_mod_cast hb
  -- Feed the resulting actual linear Hessian growth back into the mixed inequality to retain the exact constant term 2.
  have hlinear {x : E} (hx : x∈ball 0 ρ) : ‖H x‖≤1+16*‖x‖ := by
    have hn := hcoarse.norm_sub_le hx (mem_ball_self hρ)
    rw [h₀,sub_zero] at hn
    calc
      _ ≤ ‖H x-ContinuousLinearMap.id ℝ E‖+‖ContinuousLinearMap.id ℝ E‖ := by
        simpa only [sub_add_cancel] using norm_add_le (H x-ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
      _ ≤ _ := by norm_num at hn; linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)]
  refine ⟨min ρ 1,lt_min hρ (by norm_num),(min_le_left _ _).trans (min_le_left _ _),min_le_right _ _,?_⟩
  intro R hR hRr
  have hRρ : R≤ρ := hRr.trans (min_le_left _ _)
  have hR1 : R≤1 := hRr.trans (min_le_right _ _)
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hD x (hsub (ball_subset_ball hRρ hx))).hasFDerivWithinAt) _ (convex_ball 0 R)
  intro x hx
  have hxnorm : ‖x‖≤R := (mem_ball_zero_iff.mp hx).le
  have hHx : ‖H x‖≤(1+16*R)^2 := by
    have hn := hlinear (ball_subset_ball hRρ hx)
    nlinarith [sq_nonneg (16*R)]
  have hb := selfConcordant_mixed_derivative_norm_le (H x) (D x) (hsc x (hsub (ball_subset_ball hRρ hx)))
    (by positivity : (0 : ℝ)≤1+16*R) hHx
  have hR2 : R^2≤R := by nlinarith
  have hR3 : R^3≤R := by nlinarith [mul_le_mul_of_nonneg_left hR2 hR.le]
  have hb' : ‖D x‖≤2+10000*R := by nlinarith
  have hb'' : ‖D x‖≤(Real.toNNReal (2+10000*R) : ℝ) := by
    rw [Real.coe_toNNReal' _,max_eq_left (by positivity)]
    exact hb'
  exact_mod_cast hb''

end
end krylov.Nonlinear
