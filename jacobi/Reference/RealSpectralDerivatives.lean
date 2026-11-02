import jacobi.Reference.SlopeCauchy
import jacobi.Reference.SharpDerivativeLow

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The sharp original energy derivative bounds hold uniformly on real
energy half-lines. Their genuine real mean-value inequalities control
both the original solution and its actual spatial slope between the
two original spectral values. These are the quantitative inputs for
termwise spatial differentiation of the regularized GL kernel.
Use: realSlope_energy_lipschitz controls the genuine spatial derivative of the source spectral difference in Appendix C.2 (c).
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual real spatial slope of the original reference solution at real energy.
Use: realSlope_energy_lipschitz controls the genuine spatial derivative of the source spectral difference in Appendix C.2 (c).
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
-/
def realSlope (a E t : ℝ) : ℝ := (solutionSlope a (E:ℂ) t).re

/-- Every real energy above a genuine squared frequency threshold has the original positive real square-root frequency.
Use: transfers the proved original frequency derivative estimates to uniform bounds on real energy half-lines.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: nonnegativity of the shifted energy gives the true square-root
square; monotonicity of the square root preserves the prescribed positive threshold. -/
theorem real_energy_frequency {a E r : ℝ} (hr : 0<r)
    (hE : r^2≤E- jacobi.Jacobi.endpointCorrection a) :
    r≤Real.sqrt (E- jacobi.Jacobi.endpointCorrection a) ∧
      (Real.sqrt (E- jacobi.Jacobi.endpointCorrection a))^2=E- jacobi.Jacobi.endpointCorrection a := by
  have hnon : 0≤E- jacobi.Jacobi.endpointCorrection a := (sq_nonneg r).trans hE
  exact ⟨(Real.le_sqrt hr.le hnon).mpr hE,Real.sq_sqrt hnon⟩

/-- The actual energy derivative of the original solution has the sharp uniform inverse-frequency gain on real energy half-lines.
Use: realSolution_energy_lipschitz_sharp gives the additional inverse index needed when a spectral difference is multiplied by a spatial slope in F.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: choose the actual positive real square-root frequency.
The proved sharp energy bound has t<=1 and its minimum is at most
omega^(-gamma). Both inverse powers decrease above the true frequency threshold. -/
theorem solution_energy_deriv_real_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ r E:ℝ,1≤r → r^2≤E- jacobi.Jacobi.endpointCorrection a →
      ∀ t∈Icc (0:ℝ) (1/2),‖deriv (fun z => solution a z t) (E:ℂ)‖≤C*r^(-gamma a)/r := by
  -- The original entire energy function is evaluated at the same actual real energy E.
  obtain ⟨C,hC,hbound⟩ := sharp_energy_derivative ha 0
  refine ⟨C,hC,fun r E hr hE t ht => ?_⟩
  let w := Real.sqrt (E- jacobi.Jacobi.endpointCorrection a)
  have hrp : 0<r := lt_of_lt_of_le zero_lt_one hr
  obtain ⟨hwr,hws⟩ := real_energy_frequency hrp hE
  have hwp : 0<w := hrp.trans_le hwr
  have hn : ‖(w:ℂ)‖=w := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hwp]
  have he : ((jacobi.Jacobi.endpointCorrection a:ℂ)+(w:ℂ)^2)=(E:ℂ) := by
    have hw : w^2=E- jacobi.Jacobi.endpointCorrection a := hws
    rw [← Complex.ofReal_pow,← Complex.ofReal_add]
    congr 1
    linarith
  have hb := hbound (w:ℂ) (by rw [hn]; exact hr.trans hwr) (by simp) t ht
  rw [he,hn] at hb
  have hpow : w^(-gamma a)≤r^(-gamma a) :=
    Real.rpow_le_rpow_of_nonpos hrp hwr (by linarith [(parameters ha).1])
  have hm := min_le_right (t^(gamma a)) (w^(-gamma a))
  have hc : C*t/w≤C/r := by
    apply (div_le_div_iff₀ hwp hrp).mpr
    have htr : t*r≤w := by nlinarith [ht.2,hwr]
    nlinarith
  exact hb.trans ((mul_le_mul hc (hm.trans hpow)
    (le_min (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg hwp.le _))
    (by positivity : 0≤C/r)).trans_eq (by ring))

/-- The actual energy derivative of the original spatial slope has its sharp uniform size on every sufficiently high real energy half-line.
Use: realSlope_energy_lipschitz controls the true source spatial spectral differences without a formal mixed-derivative assumption.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: take the actual positive real square-root frequency, apply the
proved genuine slope energy derivative bound and decrease its negative
frequency power to the prescribed real threshold. -/
theorem slope_energy_deriv_real_bound {a : ℝ} (ha : -1<a) {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ,0<C ∧ ∀ r E:ℝ,2*max 1 (1/d)≤r →
      r^2≤E- jacobi.Jacobi.endpointCorrection a → ∀ t∈Icc d (1/2),
        ‖deriv (fun z => solutionSlope a z t) (E:ℂ)‖≤C*r^(-gamma a) := by
  -- All half-line bounds are consequences for the actual source energy function, not hypotheses on a surrogate derivative.
  obtain ⟨C,hC,hbound⟩ := slope_energy_deriv_bound ha hd
  refine ⟨C,hC,fun r E hr hE t ht => ?_⟩
  have hrp : 0<r := by linarith [le_max_left 1 (1/d)]
  obtain ⟨hwr,hws⟩ := real_energy_frequency hrp hE
  let w := Real.sqrt (E- jacobi.Jacobi.endpointCorrection a)
  have he : ((jacobi.Jacobi.endpointCorrection a:ℂ)+(w:ℂ)^2)=(E:ℂ) := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_add]
    congr 1
    linarith
  have hb := hbound w (hr.trans hwr) t ht
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hrp hwr (by linarith [(parameters ha).1])) hC.le)

/-- The actual original real solution has a sharp energy Lipschitz bound with the additional inverse-frequency factor.
Use: the original f(sigma_k)-f(tau_k) is O(k^(-gamma-3)), making the spatial derivative of the spectral tensor difference summable after norm division.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: restrict the actual entire energy function to the real axis.
Its proved complex energy derivative bounds the real derivative;
apply the mean-value inequality on the genuine convex high-energy half-line. -/
theorem realSolution_energy_lipschitz_sharp {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ r:ℝ,1≤r → ∀ E F:ℝ,
      r^2≤E- jacobi.Jacobi.endpointCorrection a → r^2≤F- jacobi.Jacobi.endpointCorrection a →
      ∀ t∈Icc (0:ℝ) (1/2),
        |realSolution a F t-realSolution a E t|≤(C*r^(-gamma a)/r)*|F-E| := by
  -- Both original real energies lie in the same proved convex derivative-control region.
  obtain ⟨C,hC,hbound⟩ := solution_energy_deriv_real_bound ha
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

/-- The actual spatial slope has the original sharp energy Lipschitz bound uniformly away from the singular endpoint.
Use: the actual partial_t f(sigma_k)-partial_t f(tau_k) is O(k^(-gamma-2)), one of the two terms in the spatial derivative bound for the regularized F summands.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the actual source slope is entire in energy. Restrict it to
the real axis and apply the genuine mean-value inequality with its
proved uniform energy derivative bound on the actual spectral half-line. -/
theorem realSlope_energy_lipschitz {a : ℝ} (ha : -1<a) {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ,0<C ∧ ∀ r:ℝ,2*max 1 (1/d)≤r → ∀ E F:ℝ,
      r^2≤E- jacobi.Jacobi.endpointCorrection a → r^2≤F- jacobi.Jacobi.endpointCorrection a →
      ∀ t∈Icc d (1/2),|realSlope a F t-realSlope a E t|≤C*r^(-gamma a)*|F-E| := by
  -- The real derivative is the real part of the true complex derivative of the same original spatial slope.
  obtain ⟨C,hC,hbound⟩ := slope_energy_deriv_real_bound ha hd
  refine ⟨C,hC,fun r hr E F hE hF t ht => ?_⟩
  let D := Ici (r^2+ jacobi.Jacobi.endpointCorrection a)
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨hd.trans_le ht.1,by linarith [ht.2]⟩
  have hderiv (x : ℝ) : HasDerivAt (fun E => realSlope a E t)
      (deriv (fun z => solutionSlope a z t) (x:ℂ)).re x :=
    (solutionSlope_energy_analytic ha ht' (x:ℂ)).differentiableAt.hasDerivAt.real_of_complex
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (fun x (_ : x∈D) => (hderiv x).differentiableAt)
    (fun x (hx : x∈D) => by
      rw [(hderiv x).deriv,Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (hbound r x hr (by change _≤x at hx; linarith) t ht))
    (convex_Ici _) (show E∈D by change _≤E; linarith) (show F∈D by change _≤F; linarith)
  simpa only [Real.norm_eq_abs] using hh

end
end jacobi.Reference
