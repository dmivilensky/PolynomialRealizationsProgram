import jacobi.Analytic.KernelTerms
import jacobi.Analytic.ReferenceEnergyPerturbation

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
One summable inverse-square majorant bounds every actual continued GL
summand on the full closed order disk and physical square. The original
spectral factors, infinite products and norm quotients are retained.
Use: proves normal convergence, joint continuity and holomorphic dependence of the original infinite GL kernel series.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter jacobi.ComplexReference jacobi.Hankel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every actual complex-order GL summand satisfies the printed uniform inverse-square bound, at all original spectral indices.
Use: proves normal convergence, joint continuity and holomorphic dependence of the original infinite GL kernel series.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: split the literal bilinear numerator into the norming-product error and two genuine reference-energy differences. Their proved full-index bounds give the squared reference amplitude times an inverse-square index factor. The actual nonzero norm quotient has the same squared amplitude as a uniform positive lower bound, so these powers cancel exactly. -/
theorem OrderDisk.kernelTerm_uniform_bound {a0 : ℝ} (D : OrderDisk a0) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius → ∀ k : ℕ,
      ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
        ‖D.kernelTerm k t s a‖≤C/(k+1:ℝ)^2 := by
  -- All factors in this estimate are the genuine functions, with every uniform premise already proved.
  obtain ⟨A,hA,hsolutions⟩ := D.reference_spectral_bounds
  obtain ⟨R,hR,hrho⟩ := D.normingRatio_bounds
  obtain ⟨c,_,hc,_,hnorm⟩ := norming_bounds (isCompact_closedBall (a0:ℂ) D.radius) (by
    intro a ha
    have har := D.admissible (by simpa only [mem_closedBall,dist_eq_norm] using ha)
    unfold gamma
    norm_num
    linarith)
  refine ⟨(R*A^2+2*A^2)/c,by positivity,fun a ha k t ht s hs => ?_⟩
  have hkp : 0<(k+1:ℝ) := by positivity
  let p : ℝ := (k+1:ℝ)^(-(gamma a).re)
  have hp : 0<p := Real.rpow_pos_of_pos hkp _
  have hpsq : p^2=1/(k+1:ℝ)^(2*(gamma a).re) := by
    dsimp [p]
    rw [Real.rpow_neg hkp.le,show 2*(gamma a).re=(gamma a).re*2 by ring,
      Real.rpow_mul hkp.le,Real.rpow_two,inv_pow,one_div]
  have hN : c*p^2≤‖norming a k‖ := by
    rw [hpsq]
    simpa only [mul_one_div] using (hnorm a
      (by simpa only [mem_closedBall,dist_eq_norm] using ha) k).1
  have hsol (u : ℝ) (hu : u∈Icc 0 (1/2)) :
      ‖solution a (D.spectrum k a) u‖≤A*p ∧
      ‖solution a (frequencyReference a k) u‖≤A*p ∧
      ‖solution a (D.spectrum k a) u-solution a (frequencyReference a k) u‖≤A*p/(k+1:ℝ)^2 := by
    simpa only [p,Real.rpow_neg hkp.le,div_eq_mul_inv,mul_inv,mul_assoc] using hsolutions a ha k u hu
  obtain ⟨hbt,hrt,hdt⟩ := hsol t ht
  obtain ⟨hbs,hrs,hds⟩ := hsol s hs
  have hweight := (hrho a ha k).2
  have hnum : ‖D.normingRatio k a*solution a (D.spectrum k a) t*solution a (D.spectrum k a) s-
      solution a (frequencyReference a k) t*solution a (frequencyReference a k) s‖≤
        ((R*A^2+2*A^2)*p^2)/(k+1:ℝ)^2 := by
    have he : D.normingRatio k a*solution a (D.spectrum k a) t*solution a (D.spectrum k a) s-
        solution a (frequencyReference a k) t*solution a (frequencyReference a k) s=
        (D.normingRatio k a-1)*solution a (D.spectrum k a) t*solution a (D.spectrum k a) s+
        (solution a (D.spectrum k a) t-solution a (frequencyReference a k) t)*solution a (D.spectrum k a) s+
        solution a (frequencyReference a k) t*(solution a (D.spectrum k a) s-solution a (frequencyReference a k) s) := by ring
    rw [he]
    calc
      _ ≤ ‖(D.normingRatio k a-1)*solution a (D.spectrum k a) t*solution a (D.spectrum k a) s‖+
        ‖(solution a (D.spectrum k a) t-solution a (frequencyReference a k) t)*solution a (D.spectrum k a) s‖+
        ‖solution a (frequencyReference a k) t*(solution a (D.spectrum k a) s-solution a (frequencyReference a k) s)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (R/(k+1:ℝ)^2)*(A*p)*(A*p)+(A*p/(k+1:ℝ)^2)*(A*p)+(A*p)*(A*p/(k+1:ℝ)^2) := by
        simp only [norm_mul]
        gcongr
      _ = _ := by ring
  rw [OrderDisk.kernelTerm,norm_div]
  have hh := div_le_div₀ (show 0≤((R*A^2+2*A^2)*p^2)/(k+1:ℝ)^2 by positivity)
    hnum (mul_pos hc (sq_pos_of_pos hp)) hN
  exact hh.trans_eq (by field_simp [hc.ne',hp.ne',hkp.ne'])

end
end jacobi.Analytic
