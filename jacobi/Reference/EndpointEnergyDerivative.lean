import jacobi.Reference.RealSpectralDerivatives

/-!
Article: jacobi, Proposition C.4.
Use: endpoint_energy_deriv_real_bound retains the exact physical minimum on all original real spectral segments, including their finite prefix.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The genuine sharp energy derivative estimate holds at every nonzero frequency, including the bounded-frequency range.
Use: endpoint_energy_deriv_real_bound retains the exact physical minimum on all original real spectral segments, including their finite prefix.
Article: jacobi, Proposition C.4.
Proof: reuse the proved high-frequency theorem. At bounded nonzero frequency the small spatial-frequency Cauchy estimate is stronger, since t^2<=t/|omega| and the minimum is exactly t^gamma. -/
theorem sharp_energy_derivative_nonzero {a : ℝ} (ha : -1<a) (b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ omega : ℂ,omega≠0 → |omega.im|≤b →
      ∀ t∈Icc (0:ℝ) (1/2),
        ‖deriv (fun z => solution a z t) ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖≤
          C*t/‖omega‖*min (t^(gamma a)) (‖omega‖^(-gamma a)) := by
  -- The low-frequency proof uses the actual selected solution, not a separately normalized analytic factor.
  obtain ⟨A,hA,hhigh⟩ := sharp_energy_derivative ha b
  obtain ⟨B,hB,hlow⟩ := sharp_energy_deriv_low ha
  refine ⟨A+B,by positivity,fun omega hne him t ht => ?_⟩
  have hw : 0<‖omega‖ := norm_pos_iff.mpr hne
  have hg : 0≤gamma a := by linarith [(parameters ha).1]
  by_cases hR : 1≤‖omega‖
  · exact (hhigh omega hR him t ht).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : A≤A+B) ht.1) hw.le)
      (le_min (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg hw.le _)))
  have hw1 : ‖omega‖≤1 := le_of_not_ge hR
  have htR : t^(gamma a)≤‖omega‖^(-gamma a) := by
    have h1 : 1≤‖omega‖^(-gamma a) := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos hw hw1 (neg_nonpos.mpr hg)
    exact (Real.rpow_le_one ht.1 (by linarith [ht.2]) hg).trans h1
  rw [min_eq_left htR]
  by_cases ht0 : t=0
  · subst t
    have hz : (fun z : ℂ => solution a z 0)=(fun _ => (0:ℂ)) := funext (solution_zero ha)
    simp only [hz,deriv_const,norm_zero,mul_zero,zero_div,zero_mul,le_refl]
  have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hs : ‖omega‖*t≤1 := by nlinarith [mul_le_mul_of_nonneg_right hw1 ht.1,ht.2]
  have ht2 : t^2≤t/‖omega‖ := (le_div_iff₀ hw).mpr (by nlinarith)
  calc
    _ ≤ B*t^(gamma a)*t^2 := hlow omega t ⟨htp,ht.2⟩ hs
    _ ≤ B*t^(gamma a)*(t/‖omega‖) := mul_le_mul_of_nonneg_left ht2 (by positivity)
    _ ≤ (A+B)*t/‖omega‖*t^(gamma a) := by
      have h := mul_le_mul_of_nonneg_right (show B≤A+B by linarith)
        (mul_nonneg (Real.rpow_nonneg ht.1 (gamma a)) (div_nonneg ht.1 hw.le))
      convert h using 1 <;> ring

/-- The actual real energy derivative retains the full endpoint-sensitive minimum uniformly above every positive frequency threshold.
Use: realSolution_endpoint_lipschitz transfers the original spectral displacement with the endpoint factor t intact.
Article: jacobi, Proposition C.4.
Proof: choose the actual positive square-root frequency. Both its reciprocal and its negative power decrease above the prescribed positive threshold; retain the unchanged spatial factor and minimum. -/
theorem endpoint_energy_deriv_real_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ r E : ℝ,0<r → r^2≤E- jacobi.Jacobi.endpointCorrection a →
      ∀ t∈Icc (0:ℝ) (1/2),‖deriv (fun z => solution a z t) (E:ℂ)‖≤
        C*t/r*min (t^(gamma a)) (r^(-gamma a)) := by
  -- No normalization of the actual derivative loses its physical endpoint factor.
  obtain ⟨C,hC,hbound⟩ := sharp_energy_derivative_nonzero ha 0
  refine ⟨C,hC,fun r E hr hE t ht => ?_⟩
  let w := Real.sqrt (E- jacobi.Jacobi.endpointCorrection a)
  obtain ⟨hwr,hws⟩ := real_energy_frequency hr hE
  have hwp : 0<w := hr.trans_le hwr
  have hn : ‖(w:ℂ)‖=w := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hwp]
  have he : ((jacobi.Jacobi.endpointCorrection a:ℂ)+(w:ℂ)^2)=(E:ℂ) := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_add]
    congr 1
    linarith
  have hb := hbound (w:ℂ) (Complex.ofReal_ne_zero.mpr hwp.ne') (by simp) t ht
  rw [he,hn] at hb
  exact hb.trans (mul_le_mul
    (div_le_div_of_nonneg_left (mul_nonneg hC.le ht.1) hr hwr)
    (min_le_min le_rfl (Real.rpow_le_rpow_of_nonpos hr hwr (by linarith [(parameters ha).1])))
    (le_min (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg hwp.le _))
    (div_nonneg (mul_nonneg hC.le ht.1) hr.le))

/-- The genuine real source solution has the full endpoint-sensitive energy mean-value bound above every positive real frequency threshold.
Use: the actual sigma/tau solution difference and the transformed-wave comparison in Proposition C.4 keep a common all-index endpoint minimum.
Article: jacobi, Proposition C.4.
Proof: restrict the original entire energy function to the real axis and apply the genuine mean-value inequality on the same convex energy half-line using its proved endpoint-sensitive derivative bound. -/
theorem realSolution_endpoint_lipschitz {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ r : ℝ,0<r → ∀ E F : ℝ,
      r^2≤E- jacobi.Jacobi.endpointCorrection a → r^2≤F- jacobi.Jacobi.endpointCorrection a →
      ∀ t∈Icc (0:ℝ) (1/2),|realSolution a F t-realSolution a E t|≤
        (C*t/r*min (t^(gamma a)) (r^(-gamma a)))*|F-E| := by
  -- The derivative and both energies concern the identical original solution on one genuine convex segment.
  obtain ⟨C,hC,hbound⟩ := endpoint_energy_deriv_real_bound ha
  refine ⟨C,hC,fun r hr E F hE hF t ht => ?_⟩
  let D := Ici (r^2+ jacobi.Jacobi.endpointCorrection a)
  have hd (x : ℝ) : HasDerivAt (fun E => realSolution a E t)
      (deriv (fun z => solution a z t) (x:ℂ)).re x :=
    (solution_energy_analytic_half ha ht (x:ℂ)).differentiableAt.hasDerivAt.real_of_complex
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (fun x (_ : x∈D) => (hd x).differentiableAt)
    (fun x (hx : x∈D) => by
      rw [(hd x).deriv,Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (hbound r x hr (by change _≤x at hx; linarith) t ht))
    (convex_Ici _) (show E∈D by change _≤E; linarith) (show F∈D by change _≤F; linarith)
  simpa only [Real.norm_eq_abs] using hh

end
end jacobi.Reference
