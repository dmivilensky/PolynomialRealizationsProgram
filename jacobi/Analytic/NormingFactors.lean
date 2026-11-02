import jacobi.Analytic.OrderDisk
import jacobi.Reference.IndexMajorant
import jacobi.Reference.NormingRatios

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The original spectral-gap factors are continued on the actual Bessel
order disk. Their perturbations have a summable majorant independent
of the complex order, with total mass of inverse-square size in the
original row index. The argument reuses the real index majorant.
Use: its product is the original norming ratio in the analytic GL kernel.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter jacobi.Hankel jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal continued spectral-gap ratio, with the omitted diagonal set to one.
Use: its product is the original norming ratio in the analytic GL kernel.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.normingFactor {a0 : ℝ} (D : OrderDisk a0) (k l : ℕ) (a : ℂ) : ℂ :=
  if l=k then 1 else (frequencyReference a l-frequencyReference a k)/(D.spectrum l a-D.spectrum k a)

/-- The continued norming ratio is the actual product of the original continued spectral-gap factors.
Use: fixes the GL weights before proving their convergence and holomorphy.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.normingRatio {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) (a : ℂ) : ℂ :=
  ∏' l,D.normingFactor k l a

/-- Distinct one-based squared natural indices have strictly positive absolute gap.
Use: turns the actual uniform spectral separation into nonvanishing of every product denominator.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: equality of the squares of two positive real indices would imply equality of the original natural indices. -/
theorem quadratic_gap_pos {k l : ℕ} (hkl : k≠l) :
    0 < |(l+1:ℝ)^2-(k+1:ℝ)^2| := by
  apply abs_pos.mpr
  intro he
  have hh : (l+1:ℝ)=(k+1:ℝ) := (sq_eq_sq₀ (by positivity) (by positivity)).mp (sub_eq_zero.mp he)
  exact hkl (by exact_mod_cast (by linarith : (k:ℝ)=l))

/-- Every genuine continued off-diagonal spectral gap stays nonzero on the full closed order disk.
Use: all factors are holomorphic quotients on a neighborhood of the open GL disk.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the proved Bessel separation bounds the gap norm below by a strictly positive constant times the positive squared-index gap. -/
theorem OrderDisk.gap_ne_zero {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) {k l : ℕ} (hkl : k≠l) :
    D.spectrum l a-D.spectrum k a≠0 :=
  norm_pos_iff.mp ((mul_pos D.gap_pos (quadratic_gap_pos hkl)).trans_le (D.separation a ha k l hkl))

/-- Each original continued product factor is holomorphic throughout the actual order disk.
Use: normal convergence of the finite products gives holomorphy of the genuine norming ratio.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the reference values are polynomials in the complex order and the actual spectral branches are holomorphic. Their denominator never vanishes off the omitted diagonal. -/
theorem OrderDisk.normingFactor_holomorphic {a0 : ℝ} (D : OrderDisk a0) (k l : ℕ) :
    DifferentiableOn ℂ (D.normingFactor k l) (ball (a0:ℂ) D.radius) := by
  -- The actual Bessel branches, rather than independent replacement spectra, enter every quotient.
  change DifferentiableOn ℂ (fun a => if l=k then 1 else
    (frequencyReference a l-frequencyReference a k)/(D.spectrum l a-D.spectrum k a)) _
  by_cases hlk : l=k
  · simp only [hlk,ite_true]
    exact differentiableOn_const 1
  simp only [hlk,ite_false]
  have hs (j : ℕ) : DifferentiableOn ℂ (D.spectrum j) (ball (a0:ℂ) D.radius) :=
    (D.holomorphic j).mono (ball_subset_ball (by linarith [D.radius_pos]))
  have ht (j : ℕ) : Differentiable ℂ (fun a : ℂ => frequencyReference a j) := by
    unfold frequencyReference frequencyGrid besselCoefficient
    fun_prop
  exact
    ((ht l).differentiableOn.sub (ht k).differentiableOn).div ((hs l).sub (hs k))
      (fun a ha => D.gap_ne_zero (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha)) (Ne.symm hlk))

/-- Every genuine continued gap factor is continuous on the closed estimation disk.
Use: the community uniform infinite-product theorem applies on this compact disk.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: both branches are holomorphic on the strictly larger disk, and the actual closed-disk gap is nonzero. -/
theorem OrderDisk.normingFactor_continuousOn {a0 : ℝ} (D : OrderDisk a0) (k l : ℕ) :
    ContinuousOn (D.normingFactor k l) (closedBall (a0:ℂ) D.radius) := by
  -- The extra open neighborhood in OrderDisk supplies continuity also at its closed boundary.
  change ContinuousOn (fun a => if l=k then 1 else
    (frequencyReference a l-frequencyReference a k)/(D.spectrum l a-D.spectrum k a)) _
  by_cases hlk : l=k
  · simp only [hlk,ite_true]
    exact continuousOn_const
  simp only [hlk,ite_false]
  have hs (j : ℕ) : ContinuousOn (D.spectrum j) (closedBall (a0:ℂ) D.radius) :=
    (D.holomorphic j).continuousOn.mono (closedBall_subset_ball (by linarith [D.radius_pos]))
  have ht (j : ℕ) : Continuous (fun a : ℂ => frequencyReference a j) := by
    unfold frequencyReference frequencyGrid besselCoefficient
    fun_prop
  exact
    ((ht l).continuousOn.sub (ht k).continuousOn).div ((hs l).sub (hs k))
      (fun a ha => D.gap_ne_zero (by simpa only [mem_closedBall,dist_eq_norm] using ha) (Ne.symm hlk))

/-- One explicit positive two-series majorant bounds the perturbation of every actual continued factor.
Use: supplies a summable bound uniform in complex order, without a logarithmic branch choice.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: factor-minus-one is the difference of the two genuine spectral displacements divided by the actual spectral gap. Insert the proved closed-disk error and gap bounds, then reuse the original translated inverse-square index inequality. -/
theorem OrderDisk.normingFactor_bound {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) (k l : ℕ) :
    ‖D.normingFactor k l a-1‖≤(D.errorConstant/D.gapConstant)*
      (2/(l+1:ℝ)^2+3*distanceMajorant k l)/(k+1:ℝ)^2 := by
  -- The diagonal contributes zero and every other denominator is the actual separated Bessel gap.
  have hC := D.error_pos.le
  have hc := D.gap_pos.le
  have hm : 0≤distanceMajorant k l := by unfold distanceMajorant; positivity
  by_cases hlk : l=k
  · rw [OrderDisk.normingFactor,ite_eq_left hlk,sub_self,norm_zero]
    positivity
  have hkl : k≠l := Ne.symm hlk
  have hQ := quadratic_gap_pos hkl
  have hgap := D.separation a ha k l hkl
  have hd := D.gap_ne_zero ha hkl
  have hdp : 0<‖D.spectrum l a-D.spectrum k a‖ := norm_pos_iff.mpr hd
  have hn : ‖(frequencyReference a l-frequencyReference a k)-(D.spectrum l a-D.spectrum k a)‖≤
      D.errorConstant/(k+1:ℝ)^2+D.errorConstant/(l+1:ℝ)^2 := by
    calc
      _ = ‖(D.spectrum k a-frequencyReference a k)-(D.spectrum l a-frequencyReference a l)‖ := by congr 1; ring
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (D.error a ha k) (D.error a ha l))
  simp only [OrderDisk.normingFactor,hlk,ite_false]
  rw [div_sub_one hd,norm_div]
  calc
    _ ≤ (D.errorConstant/(k+1:ℝ)^2+D.errorConstant/(l+1:ℝ)^2)/
        (D.gapConstant*|(l+1:ℝ)^2-(k+1:ℝ)^2|) :=
      div_le_div₀ (by positivity) hn (mul_pos D.gap_pos hQ) hgap
    _ = (D.errorConstant/D.gapConstant)*
        ((1/(k+1:ℝ)^2+1/(l+1:ℝ)^2)/|(l+1:ℝ)^2-(k+1:ℝ)^2|) := by ring
    _ ≤ _ := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (inverse_square_gap_majorant hkl)
        (div_pos D.error_pos D.gap_pos).le

end
end jacobi.Analytic
