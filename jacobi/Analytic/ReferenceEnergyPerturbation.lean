import jacobi.Analytic.ReferenceEnergyBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Actual energy derivatives and spectral displacement estimates, uniform
in complex order, physical position and every original spectral index.
Unit-radius Cauchy bounds suffice for the claimed normal kernel series.
Use: controls the actual target-reference solution displacement in the analytic GL series.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric jacobi.ComplexReference jacobi.Hankel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The genuine energy derivative has one uniform index-power bound on every fixed-radius original reference energy tube.
Use: controls the actual target-reference solution displacement in the analytic GL series.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: enlarge the reference tube radius by one. Every actual unit Cauchy circle is then inside the proved amplitude tube. The original energy solution is entire, so its derivative is the community Cauchy derivative and has the same bound. -/
theorem OrderDisk.reference_energy_deriv_bound {a0 : ℝ} (D : OrderDisk a0)
    {E : ℝ} (hE : 0≤E) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius → ∀ k : ℕ,
      ∀ z : ℂ,‖z-frequencyReference a k‖≤E → ∀ t∈Icc (0:ℝ) (1/2),
        ‖deriv (fun w => solution a w t) z‖≤C/(k+1:ℝ)^(gamma a).re := by
  -- The Cauchy circles use the defining entire energy function, including at zero frequency.
  obtain ⟨C,hC,hbound⟩ := D.reference_energy_bound (E := E+1) (by linarith)
  refine ⟨C,hC,fun a ha k z hz t ht => ?_⟩
  have hag : 0<(gamma a).re := by have har := D.admissible ha; unfold gamma; norm_num; linarith
  have hd : DifferentiableOn ℂ (fun w => solution a w t) univ :=
    fun w _ => (solution_energy_analytic hag ⟨ht.1,by linarith [ht.2]⟩ w).differentiableAt.differentiableWithinAt
  rw [← Complex.cderiv_eq_deriv isOpen_univ hd (by norm_num : (0:ℝ)<1) (subset_univ _)]
  have hh := Complex.norm_cderiv_le (by norm_num : (0:ℝ)<1) (f := fun w => solution a w t)
    (z := z) (fun w hw => hbound a ha k w (by
      have hdist : ‖w-z‖≤1 := by simpa only [mem_closedBall,dist_eq_norm] using sphere_subset_closedBall hw
      have htri := norm_sub_le_norm_sub_add_norm_sub w z (frequencyReference a k)
      linarith) t ht)
  simpa only [div_one] using hh

/-- The genuine complex-order reference solution has a uniform energy Lipschitz bound on each original reference energy tube.
Use: compares f(t,sigma_k) and f(t,tau_k) on their actual complex spectral segment.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the reference tube is a convex complex disk. The proved genuine energy derivative bound applies everywhere on it, and the community complex mean value inequality bounds the difference of the original endpoint values. -/
theorem OrderDisk.reference_energy_lipschitz {a0 : ℝ} (D : OrderDisk a0)
    {E : ℝ} (hE : 0≤E) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius → ∀ k : ℕ,
      ∀ z w : ℂ,‖z-frequencyReference a k‖≤E → ‖w-frequencyReference a k‖≤E →
        ∀ t∈Icc (0:ℝ) (1/2),
          ‖solution a w t-solution a z t‖≤C/(k+1:ℝ)^(gamma a).re*‖w-z‖ := by
  -- Convexity is used for the actual complex energies, with no restriction to a real segment.
  obtain ⟨C,hC,hbound⟩ := D.reference_energy_deriv_bound hE
  refine ⟨C,hC,fun a ha k z w hz hw t ht => ?_⟩
  have hag : 0<(gamma a).re := by have har := D.admissible ha; unfold gamma; norm_num; linarith
  exact Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
    (fun u (_ : u∈closedBall (frequencyReference a k) E) =>
      (solution_energy_analytic hag ⟨ht.1,by linarith [ht.2]⟩ u).differentiableAt)
    (fun u hu => hbound a ha k u (by simpa only [mem_closedBall,dist_eq_norm] using hu) t ht)
    (convex_closedBall _ _) (by simpa only [mem_closedBall,dist_eq_norm] using hz)
    (by simpa only [mem_closedBall,dist_eq_norm] using hw)

/-- Both original reference amplitudes and their genuine target-reference difference have uniform full-index bounds on the actual complex spectral disk.
Use: together with the proved norming products and norm lower bound, gives the summable original GL kernel majorant.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual inverse-square spectral displacement lies in the fixed reference energy tube. Apply the full-index amplitude and complex Lipschitz bounds there, multiply by the proved original spectral error, and enlarge the two constants to one common coefficient. -/
theorem OrderDisk.reference_spectral_bounds {a0 : ℝ} (D : OrderDisk a0) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius → ∀ k : ℕ,
      ∀ t∈Icc (0:ℝ) (1/2),
        ‖solution a (D.spectrum k a) t‖≤C/(k+1:ℝ)^(gamma a).re ∧
        ‖solution a (frequencyReference a k) t‖≤C/(k+1:ℝ)^(gamma a).re ∧
        ‖solution a (D.spectrum k a) t-solution a (frequencyReference a k) t‖≤
          C/((k+1:ℝ)^(gamma a).re*(k+1:ℝ)^2) := by
  -- The same constants cover the whole closed disk, all physical positions and the genuine finite prefix.
  obtain ⟨A,hA,hamp⟩ := D.reference_energy_bound D.error_pos.le
  obtain ⟨B,hB,hlip⟩ := D.reference_energy_lipschitz D.error_pos.le
  have hE := D.error_pos
  refine ⟨A+B*D.errorConstant,by positivity,fun a ha k t ht => ?_⟩
  have hsq : 1≤(k+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have herr := D.error a ha k
  have hS : ‖D.spectrum k a-frequencyReference a k‖≤D.errorConstant :=
    herr.trans (div_le_self D.error_pos.le hsq)
  have hT : ‖frequencyReference a k-frequencyReference a k‖≤D.errorConstant := by
    simpa only [sub_self,norm_zero] using D.error_pos.le
  have hconst : A≤A+B*D.errorConstant := by linarith [mul_pos hB hE]
  refine ⟨(hamp a ha k _ hS t ht).trans (div_le_div_of_nonneg_right hconst (by positivity)),
    (hamp a ha k _ hT t ht).trans (div_le_div_of_nonneg_right hconst (by positivity)),?_⟩
  calc
    _ ≤ B/(k+1:ℝ)^(gamma a).re*‖D.spectrum k a-frequencyReference a k‖ :=
      hlip a ha k _ _ hT hS t ht
    _ ≤ B/(k+1:ℝ)^(gamma a).re*(D.errorConstant/(k+1:ℝ)^2) :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    _ = (B*D.errorConstant)/((k+1:ℝ)^(gamma a).re*(k+1:ℝ)^2) := by rw [div_mul_div_comm]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end
end jacobi.Analytic
