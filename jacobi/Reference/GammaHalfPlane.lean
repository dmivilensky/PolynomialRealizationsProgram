import jacobi.Reference.GammaVerticalQuotient
import jacobi.Complex.HalfPlaneBound

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The actual power-normalized Gamma quotient is bounded on the whole
closed right half-plane. Its genuine negative-energy asymptotic
controls the imaginary boundary, and the proved polynomial growth
allows the Phragmen--Lindelof principle to transfer that bound inside.
Use: gamma_vertical_normalized_bound controls both boundary rays from the proved positive-ray asymptotic.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The modulus of the actual normalized Gamma quotient is even on the imaginary axis.
Use: gamma_vertical_normalized_bound controls both boundary rays from the proved positive-ray asymptotic.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Schwarz reflection of the Gamma function.
Proof: real shifts and the normalization base conjugate under y maps to -y; complex powers with real exponent have modulus equal to the corresponding real power. -/
theorem gamma_normalized_vertical_even (a b y : ℝ) :
    ‖jacobi.Complex.normalizedGammaRatio a b (Complex.I*((-y:ℝ):ℂ))‖=
      ‖jacobi.Complex.normalizedGammaRatio a b (Complex.I*(y:ℂ))‖ := by
  -- Only moduli of powers are reflected, so there is no branch ambiguity for the normalization power.
  have ha : Complex.I*((-y:ℝ):ℂ)+(a:ℂ)=conj (Complex.I*(y:ℂ)+(a:ℂ)) := by simp
  have hb : Complex.I*((-y:ℝ):ℂ)+(b:ℂ)=conj (Complex.I*(y:ℂ)+(b:ℂ)) := by simp
  have hc : (1:ℂ)+Complex.I*((-y:ℝ):ℂ)=conj ((1:ℂ)+Complex.I*(y:ℂ)) := by simp
  simp only [jacobi.Complex.normalizedGammaRatio,norm_mul,norm_div,Complex.norm_cpow_real,
    ha,hb,hc,Complex.Gamma_conj,norm_conj]

/-- The actual normalized Gamma quotient is uniformly bounded on the whole imaginary axis.
Use: gamma_normalized_halfPlane_bound supplies this bound to the half-plane Phragmen--Lindelof theorem.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: its squared modulus has a proved positive finite limit on the positive ray, conjugation controls the negative ray, and continuity bounds the remaining compact interval. -/
theorem gamma_vertical_normalized_bound {a b : ℝ} (ha : 1/4<a) (hb : 1/4<b) :
    ∃ C : ℝ,0<C ∧ ∀ y : ℝ,‖jacobi.Complex.normalizedGammaRatio a b (Complex.I*(y:ℂ))‖≤C := by
  -- The compact bound closes the finite middle part; the asymptotic is not substituted as a global premise.
  obtain ⟨L,hL,hl⟩ := gamma_vertical_normalized_limit ha hb
  obtain ⟨Y,hY⟩ := eventually_atTop.mp ((tendsto_order.mp hl).2 (L+1) (by linarith))
  let R : ℝ := max 1 Y
  have hc : Continuous (fun y : ℝ => ‖jacobi.Complex.normalizedGammaRatio a b (Complex.I*(y:ℂ))‖) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hD : ContinuousAt (jacobi.Complex.normalizedGammaRatio a b) (Complex.I*(y:ℂ)) :=
      (jacobi.Complex.normalizedGammaRatio_differentiable
        (show 0<a by linarith) (show 0<b by linarith) (z := Complex.I*(y:ℂ)) (by simp)).continuousAt
    exact (hD.comp (f := fun x : ℝ => Complex.I*(x:ℂ)) (x := y) (by fun_prop)).norm
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).bddAbove_image hc.continuousOn
  refine ⟨max (L+2) (M+1),lt_of_lt_of_le (by linarith) (le_max_left _ _),fun y => ?_⟩
  by_cases hy : R≤|y|
  · have htail := hY |y| ((le_max_right 1 Y).trans hy)
    have he : ‖jacobi.Complex.normalizedGammaRatio a b (Complex.I*((|y|:ℝ):ℂ))‖=
        ‖jacobi.Complex.normalizedGammaRatio a b (Complex.I*(y:ℂ))‖ := by
      rcases le_or_gt 0 y with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h,gamma_normalized_vertical_even]
    rw [he] at htail
    apply le_trans (b := L+2) ?_ (le_max_left _ _)
    nlinarith [norm_nonneg (jacobi.Complex.normalizedGammaRatio a b (Complex.I*(y:ℂ)))]
  · have hyR : y∈Icc (-R) R := by
      have hh := abs_lt.mp (lt_of_not_ge hy)
      exact ⟨hh.1.le,hh.2.le⟩
    exact (hM ⟨y,hyR,rfl⟩).trans ((by linarith : M≤M+1).trans (le_max_right _ _))

/-- The actual normalized Gamma quotient is uniformly bounded throughout the closed right half-plane.
Use: gamma_halfPlane_power_bounds applies this theorem in both orders to prove the matching power lower bound for the Gamma factor in Delta_tau.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the genuine vertical bound, holomorphicity and polynomial growth satisfy the proved half-plane Phragmen--Lindelof theorem. -/
theorem gamma_normalized_halfPlane_bound {a b : ℝ} (ha : 1/4<a) (hb : 1/4<b) :
    ∃ C : ℝ,0<C ∧ ∀ z : ℂ,0≤z.re → ‖jacobi.Complex.normalizedGammaRatio a b z‖≤C := by
  obtain ⟨B,hB,n,hgrowth⟩ := jacobi.Complex.normalizedGammaRatio_polynomial_bound
    (show 0<a by linarith) (show 0<b by linarith)
  obtain ⟨C,hC,hboundary⟩ := gamma_vertical_normalized_bound ha hb
  exact ⟨C,hC,fun _ hz => jacobi.Complex.halfPlane_bound
    (fun _ h => jacobi.Complex.normalizedGammaRatio_differentiable
      (show 0<a by linarith) (show 0<b by linarith) h) hB.le hgrowth hboundary hz⟩

/-- The actual Gamma quotient satisfies its sharp uniform power upper bound on the closed right half-plane.
Use: gamma_halfPlane_power_bounds combines this result in both orders to prove the matching lower bound needed in the reflected formula for Delta_tau.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: multiply the proved normalized quotient bound by the opposite positive real power of norm(1+z); the two normalization exponents cancel exactly. -/
theorem gamma_halfPlane_power_upper {a b : ℝ} (ha : 1/4<a) (hb : 1/4<b) :
    ∃ C : ℝ,0<C ∧ ∀ z : ℂ,0≤z.re →
      ‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖≤C*‖(1:ℂ)+z‖^(a-b) := by
  -- The base stays away from zero on the entire closed half-plane, including its origin.
  obtain ⟨C,hC,hbound⟩ := gamma_normalized_halfPlane_bound ha hb
  refine ⟨C,hC,fun z hz => ?_⟩
  have hp : 0<‖(1:ℂ)+z‖ := by
    have h := Complex.re_le_norm ((1:ℂ)+z)
    simp only [add_re,one_re] at h
    linarith
  have he : ‖(1:ℂ)+z‖^(b-a)*‖(1:ℂ)+z‖^(a-b)=1 := by
    rw [← Real.rpow_add hp,show b-a+(a-b)=0 by ring,Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_right (hbound z hz)
    (Real.rpow_nonneg (norm_nonneg ((1:ℂ)+z)) (a-b))
  rw [jacobi.Complex.normalizedGammaRatio,norm_mul,Complex.norm_cpow_real,mul_assoc,he,mul_one] at hh
  exact hh

/-- The genuine Gamma quotient has matching uniform positive power bounds in the entire closed right half-plane.
Use: after the finite Gamma shift and reflection formula, this is the Gamma factor in the absolute lower contour estimate for the actual Delta_tau.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the upper bound is the half-plane maximum principle. Apply it with the shifts reversed; their nonzero Gamma quotients multiply to one, giving the reciprocal lower bound. -/
theorem gamma_halfPlane_power_bounds {a b : ℝ} (ha : 1/4<a) (hb : 1/4<b) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ z : ℂ,0≤z.re →
      c*‖(1:ℂ)+z‖^(a-b)≤‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖ ∧
      ‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖≤C*‖(1:ℂ)+z‖^(a-b) := by
  -- Both cancellations use strictly positive real parts of the actual Gamma arguments.
  obtain ⟨C,hC,hupper⟩ := gamma_halfPlane_power_upper ha hb
  obtain ⟨D,hD,hlower⟩ := gamma_halfPlane_power_upper hb ha
  refine ⟨1/D,C,one_div_pos.mpr hD,hC,fun z hz => ⟨?_,hupper z hz⟩⟩
  have hGa : Complex.Gamma (z+(a:ℂ))≠0 := Gamma_ne_zero_of_re_pos (by simp only [add_re,ofReal_re]; linarith)
  have hGb : Complex.Gamma (z+(b:ℂ))≠0 := Gamma_ne_zero_of_re_pos (by simp only [add_re,ofReal_re]; linarith)
  have hn : 0<‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖ := norm_pos_iff.mpr (div_ne_zero hGa hGb)
  have hp : 0<‖(1:ℂ)+z‖ := by
    have h := Complex.re_le_norm ((1:ℂ)+z)
    simp only [add_re,one_re] at h
    linarith
  have he : ‖(1:ℂ)+z‖^(b-a)*‖(1:ℂ)+z‖^(a-b)=1 := by
    rw [← Real.rpow_add hp,show b-a+(a-b)=0 by ring,Real.rpow_zero]
  have hq : ‖Complex.Gamma (z+(b:ℂ))/Complex.Gamma (z+(a:ℂ))‖*
      ‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖=1 := by
    rw [← norm_mul]
    field_simp [hGa,hGb]
    exact norm_one
  have h := mul_le_mul_of_nonneg_right (hlower z hz) hn.le
  rw [hq] at h
  have hh := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hp.le (a-b))
  have hh' : ‖(1:ℂ)+z‖^(a-b)≤D*‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖ := by
    calc
      _ ≤ (D*‖(1:ℂ)+z‖^(b-a)*‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖)*‖(1:ℂ)+z‖^(a-b) := by simpa only [one_mul] using hh
      _ = (D*‖Complex.Gamma (z+(a:ℂ))/Complex.Gamma (z+(b:ℂ))‖)*
          (‖(1:ℂ)+z‖^(b-a)*‖(1:ℂ)+z‖^(a-b)) := by ring
      _ = _ := by rw [he,mul_one]
  exact (by simpa only [one_div_mul_eq_div] using (div_le_iff₀ hD).mpr (hh'.trans_eq (mul_comm _ _)))

end
end jacobi.Reference
