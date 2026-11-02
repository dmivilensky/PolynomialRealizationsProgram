import krylov.Convergence.ObservableFCAverages
import krylov.Convergence.ObservableNormalization

/-!
Article: main_krylov, apG:Dunif, uniform actual FC prefix estimates.
Use: derive normalized independence, the original physical inverse domain
and the quadratic staircase residual on every true pre-stopping prefix.
Source: genuine source secants, measured conjugacy and finite coercivity.
The passed earlier observable tests replace no analytic nondegeneracy
hypothesis: they are extracted from the actual cycle execution.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every genuine FC pre-stopping prefix has a controlled real Gram,
positive lower synthesis form, an actually defined original physical solve
and a uniform quadratic residual. Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.fc_prefix_bounds {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/4) (K : ℕ)
    (hgood : ∀ j<K,ObservableFCGood (observableFCSearchRun T f G r x₀ j))
    (hsmall : (K:ℝ)*(2*(L:ℝ)*‖T x₀‖)≤1/8) :
    let s := fun i : Fin K=>observableFCCanonicalStep T f G r x₀ i.val
    let y := fun i : Fin K=>observableFCCanonicalGradient T f G r x₀ (i.val+1)-
      observableFCCanonicalGradient T f G r x₀ i.val
    ‖crossGram (unitWindow s) (unitWindow s)-1‖≤K*(2*(L:ℝ)*‖T x₀‖) ∧
    (∀ c : Fin K→ℝ,(7/8:ℝ)*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (crossGram (unitWindow s) (unitWindow s)*ᵥc)) ∧
    IsUnit (crossGram (windowImages (selectedWindow fullMemory (observableFCSearchRun T f G r x₀ K)))
      (windowSteps (selectedWindow fullMemory (observableFCSearchRun T f G r x₀ K)))).det ∧
    (∀ i,‖unitWindowImages s y i-unitWindow s i‖≤2*(L:ℝ)*‖T x₀‖) ∧
    ‖projectedResidual (unitWindow s) (observableFCCanonicalGradient T f G r x₀ K)‖≤
      16*(L:ℝ)*(K:ℝ)*Real.sqrt K*‖T x₀‖^2 := by
  have hr := S.radius_pos
  let g := observableFCCanonicalGradient T f G r x₀
  let step := observableFCCanonicalStep T f G r x₀
  let A := observableFCCanonicalOperator T f G H r x₀
  let s := fun i : Fin K=>step i.val
  let y := fun i : Fin K=>g (i.val+1)-g i.val
  let epsilon := 2*(L:ℝ)*‖T x₀‖
  have he : 0≤epsilon := by dsimp only [epsilon];positivity
  have hs (i : Fin K) : s i≠0 := by
    intro hz
    change T (observableFCSearchStep T f G r x₀ i.val)=0 at hz
    have ht := T.injective (show T (observableFCSearchStep T f G r x₀ i.val)=T 0 by
      simpa only [map_zero] using hz)
    exact S.fc_step_nonzero x₀ hx₀ i.val (hgood i.val i.isLt) ht
  have hy (i : Fin K) : ‖y i-s i‖≤epsilon*‖s i‖ := by
    have hd := S.fc_averaged_data x₀ hx₀ i.val
    change ‖(g (i.val+1)-g i.val)-step i.val‖≤_
    rw [hd.1]
    exact ((A i.val-ContinuousLinearMap.id ℝ E).le_opNorm (s i)).trans
      (mul_le_mul_of_nonneg_right hd.2.2 (norm_nonneg (s i)))
  have hconj (i j : Fin K) (hij : i<j) : inner ℝ (y i) (s j)=0 :=
    S.fc_canonical_conjugate x₀ hx₀ (by exact hij) (hgood j.val j.isLt)
  have hunit := unitWindow_norm s hs
  have herr := unitWindow_image_error s y hs hy
  have huc := conjugate_window_unit s y hconj
  have hdomains := observable_fc_coefficient_domains (unitWindow s) (unitWindowImages s y)
    hunit epsilon he herr huc hsmall
  have hgram := conjugate_window_gram_bound (unitWindow s) (unitWindowImages s y) hunit he herr huc
  have hraw := observable_raw_unit_of_normalized s y hdomains.2.2.1
  have hycoord : y=(fun i : Fin K=>T.symm (observableFCSearchSecant T f G r x₀ i.val)) := by
    funext i
    simp only [y,g,observableFCCanonicalGradient,coordinateGradient,T.symm_apply_apply,
      observableFCSearchSecant,map_sub]
  have hphysical : IsUnit (crossGram
      (fun i : Fin K=>observableFCSearchSecant T f G r x₀ i.val)
      (fun i : Fin K=>observableFCSearchStep T f G r x₀ i.val)).det := by
    rw [hycoord] at hraw
    change IsUnit (crossGram (fun i : Fin K=>T.symm (observableFCSearchSecant T f G r x₀ i.val))
      (fun i : Fin K=>T (observableFCSearchStep T f G r x₀ i.val))).det at hraw
    rw [observable_metric_crossGram T S.inverse_symmetric] at hraw
    exact hraw
  have hsolve : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (observableFCSearchRun T f G r x₀ K)))
      (windowSteps (selectedWindow fullMemory (observableFCSearchRun T f G r x₀ K)))).det := by
    rw [observableFCSearchRun_window,observable_executed_det_chronological]
    exact hphysical
  have hres := observable_fc_prefix_residual g step A K epsilon (2*‖T x₀‖) he (by positivity)
    (fun j _=>(S.fc_averaged_data x₀ hx₀ j).1)
    (fun j _=>(S.fc_averaged_data x₀ hx₀ j).2.1)
    (fun j _=>(S.fc_averaged_data x₀ hx₀ j).2.2)
    (fun j _=>S.fc_line_orthogonal x₀ hx₀ j)
    (fun i j hij hj=>S.fc_canonical_conjugate x₀ hx₀ hij (hgood j hj))
    (by
      intro j _hj hj
      have hn := norm_sub_le (T (observableFCSearchPoint T f G r x₀ (j+1)))
        (T (observableFCSearchPoint T f G r x₀ j))
      change ‖T (_-_)‖≤_
      rw [map_sub]
      exact hn.trans (by linarith only [(S.fc_localization x₀ (by linarith) j).1,
        (S.fc_localization x₀ (by linarith) (j+1)).1]))
  refine ⟨hgram,hdomains.1,hsolve,herr,?_⟩
  exact hres.trans_eq (by dsimp only [epsilon];ring)

end
end krylov.Convergence
