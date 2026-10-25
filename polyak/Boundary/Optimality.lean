import polyak.Boundary.Certificate

/-!
Article: primal–dual pairing after Lemma dualfactor, including G=1.
Use: later algebraic and interval-certified families satisfy this general criterion.
Proof: strict monotonicity gives explicit finite certificates above a feasible twist;
at G=1 equal positive minimizer weights remove the sole potentially vanishing endpoint.
-/

noncomputable section
namespace polyak.Boundary
open Spectral

/-- Article: nonnegative Q implies a nonpositive dual symbol on the entire frequency interval. -/
theorem dualSymbol_nonpos_of_polynomial (W : DualWeights) (u : ℝ) {G : ℝ} (hG : 1 ≤ G)
    (hQ : ∀ c : Frequency, 0 ≤ (dualPolynomial W u G).eval (c : ℝ)) (c : Frequency) :
    dualSymbol W u G c ≤ 0 := by
  rw [dualPolynomial_factor W u hG]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr (c.property.2.trans hG))) (hQ c)

/-- Article: explicit strict certificate at every larger nonnegative twist.
Use: the case t=0 is included and uses both minimizer constraints with equal weights. -/
theorem strictCertificate_above (W : DualWeights) (t : ℝ) {u u' : ℝ} (hu : 0 ≤ u)
    (huu' : u < u')
    (hQ : ∀ c : Frequency, 0 ≤ (dualPolynomial W u (Real.cosh t)).eval (c : ℝ)) :
    Nonempty (Duality.StrictCertificate (Waves.polyakMultiplier (Real.arsinh u')) t) := by
  have hG := Real.one_le_cosh t
  have hup : 0 < u' := hu.trans_lt huu'
  have hdiff : 0 < u'^2-u^2 := by nlinarith
  have hmono (c : Frequency) :
      dualSymbol W u' (Real.cosh t) c ≤ -(Real.cosh t-c)*(u'^2-u^2) := by
    have hm := dualSymbol_mono W hG hu huu'.le c
    have hn := dualSymbol_nonpos_of_polynomial W u hG hQ c
    linarith
  by_cases hGt : 1 < Real.cosh t
  · refine ⟨strictCertificateOfWeights W (Real.arsinh u') t 0
      ((Real.cosh t-1)*(u'^2-u^2)) le_rfl (mul_pos (by linarith) hdiff) ?_⟩
    intro c
    simp only [Real.sinh_arsinh,mul_zero,zero_mul,add_zero]
    have hc : 0 ≤ 1-(c : ℝ) := by linarith [c.property.2]
    have hprod := mul_nonneg hc hdiff.le
    nlinarith [hmono c]
  · have hG1 : Real.cosh t=1 := le_antisymm (le_of_not_gt hGt) hG
    let γ := (u'^2-u^2)/8
    have hγ : 0 < γ := by dsimp [γ]; positivity
    refine ⟨strictCertificateOfWeights W (Real.arsinh u') t γ (2*γ*u'^2) hγ.le (by positivity) ?_⟩
    intro c
    simp only [Real.sinh_arsinh]
    have hbase := hmono c
    rw [hG1] at hbase
    have hc : 0 ≤ 1-(c : ℝ) := by linarith [c.property.2]
    have hg : g u' c ≤ 2*(1-(c : ℝ))-u'^2 := by
      unfold g
      nlinarith [sq_nonneg ((c : ℝ)-1)]
    have hgm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*γ by positivity)
    have hrem : 0 ≤ (1-(c : ℝ))*(u'^2-u^2-4*γ) := by
      apply mul_nonneg hc
      dsimp [γ]
      linarith
    rw [hG1]
    nlinarith [hgm,hrem]

/-- Article: a feasible primal spectrum and a nonnegative dual polynomial identify the exact boundary.
Use: no guessed analytic branch or assumed optimality is present in this theorem. -/
theorem primal_dual_optimal (W : DualWeights) {u t C : ℝ} {ν : Spectrum}
    (hu : 0 ≤ u) (hfeasible : FeasibleU u t ν C)
    (hQ : ∀ c : Frequency, 0 ≤ (dualPolynomial W u (Real.cosh t)).eval (c : ℝ)) :
    V t = Real.arsinh u := by
  have hbase : Feasible (Real.arsinh u) t ν C := by simpa only [Feasible,Real.sinh_arsinh] using hfeasible
  have hlow : Real.arsinh u ≤ V t := (isGreatest_V t).2 ⟨ν,C,hbase⟩
  apply le_antisymm _ hlow
  by_contra h
  have hv : Real.arsinh u < V t := lt_of_not_ge h
  have hu' : u < Real.sinh (V t) := by
    simpa only [Real.sinh_arsinh] using Real.sinh_lt_sinh.mpr hv
  obtain ⟨cert⟩ := strictCertificate_above W t hu hu' hQ
  obtain ⟨ν',C',hboundary⟩ := V_mem t
  have hmix : Waves.MixtureFeasible ν' (Waves.polyakMultiplier (V t)) C' t :=
    (Waves.mixtureFeasible_polyak_iff ν' (V t) C' t).mpr hboundary
  have harg : Real.arsinh (Real.sinh (V t)) = V t := Real.arsinh_sinh _
  rw [harg] at cert
  exact cert.not_feasible ν' C' hmix

end polyak.Boundary
