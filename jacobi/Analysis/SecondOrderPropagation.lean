import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Lemma E.1.
Use: the original Bessel Hankel error is propagated from its proved real-ray Cauchy data to every bounded complex-frequency disk, with no assumed complex asymptotic remainder.
-/
namespace jacobi.Analysis
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false

/-- A genuine complex second-order error state with bounded forcing has an explicit value-and-slope bound throughout the actual unit propagation segment.
Use: the original Bessel Hankel error is propagated from its proved real-ray Cauchy data to every bounded complex-frequency disk, with no assumed complex asymptotic remainder.
Article: jacobi, Lemma E.1.
Source: Gronwall's inequality, Mathlib norm_le_gronwallBound_of_norm_deriv_right_le.
Proof: adjoin the genuine constant forcing bound D as a third state coordinate. Its actual derivative is zero, so the true three-coordinate derivative norm is at most |eta|*(K+1) times the same state norm. The community homogeneous Gronwall bound and t<=1 give the claimed exponential estimate. -/
theorem second_order_segment_bound {f g h : ℝ → ℂ} {η : ℂ} {K D δ : ℝ}
    (hK : 0≤K) (hD : 0≤D) (hDδ : D≤δ)
    (hf : ∀ t∈Icc (0:ℝ) 1,HasDerivAt f (η*g t) t)
    (hg : ∀ t∈Icc (0:ℝ) 1,HasDerivAt g (η*h t) t)
    (hh : ∀ t∈Icc (0:ℝ) 1,‖h t‖≤K*‖f t‖+D)
    (hf0 : ‖f 0‖≤δ) (hg0 : ‖g 0‖≤δ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖f t‖≤δ*Real.exp (‖η‖*(K+1)) ∧ ‖g t‖≤δ*Real.exp (‖η‖*(K+1)) := by
  -- The actual forcing is retained as a constant coordinate, making the true state inequality homogeneous.
  let S (s : ℝ) : ℂ × (ℂ × ℂ) := (f s,(g s,(D:ℂ)))
  let S' (s : ℝ) : ℂ × (ℂ × ℂ) := (η*g s,(η*h s,0))
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt S (S' s) s :=
    (hf s hs).prodMk ((hg s hs).prodMk (hasDerivAt_const s (D:ℂ)))
  have hDn : ‖(D:ℂ)‖=D := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hD]
  have hF (s : ℝ) : ‖f s‖≤‖S s‖ := by
    change ‖f s‖≤max ‖f s‖ (max ‖g s‖ ‖(D:ℂ)‖)
    exact le_max_left _ _
  have hG (s : ℝ) : ‖g s‖≤‖S s‖ := by
    change ‖g s‖≤max ‖f s‖ (max ‖g s‖ ‖(D:ℂ)‖)
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hDS (s : ℝ) : D≤‖S s‖ := by
    change D≤max ‖f s‖ (max ‖g s‖ ‖(D:ℂ)‖)
    rw [hDn]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hb (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : ‖S' s‖≤(‖η‖*(K+1))*‖S s‖ := by
    have hcurv : ‖h s‖≤(K+1)*‖S s‖ :=
      (hh s hs).trans (by nlinarith [mul_le_mul_of_nonneg_left (hF s) hK,hDS s])
    have hfirst : ‖η‖*‖g s‖≤(‖η‖*(K+1))*‖S s‖ := by
      apply (mul_le_mul_of_nonneg_left (hG s) (norm_nonneg η)).trans
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg η) hK) (norm_nonneg (S s))]
    have hsecond : ‖η‖*‖h s‖≤(‖η‖*(K+1))*‖S s‖ :=
      (mul_le_mul_of_nonneg_left hcurv (norm_nonneg η)).trans_eq (by ring)
    dsimp only [S']
    rw [Prod.norm_def,Prod.norm_def,norm_mul,norm_mul,norm_zero]
    exact max_le hfirst (max_le hsecond (by positivity))
  have hstart : ‖S 0‖≤δ := by
    change max ‖f 0‖ (max ‖g 0‖ ‖(D:ℂ)‖)≤δ
    rw [hDn]
    exact max_le hf0 (max_le hg0 hDδ)
  have hbound := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ := δ) (K := ‖η‖*(K+1)) (ε := 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt (s := Ici s)) hstart
    (fun s hs => by simpa only [add_zero] using hb s ⟨hs.1,hs.2.le⟩) t ht
  rw [sub_zero,gronwallBound_ε0] at hbound
  have hfinal : ‖S t‖≤δ*Real.exp (‖η‖*(K+1)) := hbound.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_of_le_one_right (by positivity : 0≤‖η‖*(K+1)) ht.2)) (hD.trans hDδ))
  exact ⟨(hF t).trans hfinal,(hG t).trans hfinal⟩

end
end jacobi.Analysis
