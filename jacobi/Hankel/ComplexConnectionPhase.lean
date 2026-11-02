import jacobi.Hankel.ConnectionAnalytic
import jacobi.Hankel.ConnectionNontrivial
import jacobi.Hankel.RealConnectionPhase

/-!
Article: jacobi, Lemma E.1.
Use: common_bessel_connection_phase discharges this disk's coefficient bounds from the actual quadratic Bessel coefficient; the original Bessel zero equation then has the true canonical phase uniformly for complex order.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The exact original real numbered-zero Bessel-Jost phase extends holomorphically throughout any genuine common admissible order disk.
Use: common_bessel_connection_phase discharges this disk's coefficient bounds from the actual quadratic Bessel coefficient; the original Bessel zero equation then has the true canonical phase uniformly for complex order.
Article: jacobi, Lemma E.1.
Proof: both genuine connection coefficients are analytic on the original disk. Their actual real phase identity holds along a strictly nonconstant real sequence converging to its center. The community complex identity theorem extends this equality across the connected disk. -/
theorem complex_bessel_connection_phase {R r a0 : ℝ} (hR : 0<R) (hr : 0<r)
    (ha0 : -1<a0) (hra : r≤a0+1)
    (hc : ∀ a : ℂ,‖a-(a0:ℂ)‖<r → ‖besselCoefficient a‖/R≤1/2)
    {a : ℂ} (ha : ‖a-(a0:ℂ)‖<r) :
    incomingBesselCoefficient hR a= -besselZeroPhase a*outgoingBesselCoefficient hR a := by
  -- All original order, analyticity and contraction conditions hold on the same actual connected disk.
  let U : Set ℂ := Metric.ball (a0:ℂ) r
  have hmem {b : ℂ} : b∈U ↔ ‖b-(a0:ℂ)‖<r := by
    simp only [U,Metric.mem_ball,dist_eq_norm]
  have hreal (b : ℂ) (hb : b∈U) : -1<b.re := by
    have hn := hmem.mp hb
    have hh := Complex.re_le_norm ((a0:ℂ)-b)
    rw [norm_sub_rev] at hh
    simp only [Complex.sub_re,Complex.ofReal_re] at hh
    linarith
  have hI : AnalyticOnNhd ℂ (incomingBesselCoefficient hR) U := fun b hb =>
    incomingBesselCoefficient_analytic hR (hreal b hb) ((hc b (hmem.mp hb)).trans_lt (by norm_num))
  have hO : AnalyticOnNhd ℂ (fun b => -besselZeroPhase b*outgoingBesselCoefficient hR b) U := by
    intro b hb
    have hP : AnalyticAt ℂ (fun z : ℂ => -besselZeroPhase z) b := by unfold besselZeroPhase; fun_prop
    exact hP.mul (outgoingBesselCoefficient_analytic hR (hreal b hb)
      ((hc b (hmem.mp hb)).trans_lt (by norm_num)))
  let seq (n : ℕ) : ℝ := a0+(r/2)/((n:ℝ)+1)
  have hdelta (n : ℕ) : 0<(r/2)/((n:ℝ)+1) ∧ (r/2)/((n:ℝ)+1)<r := by
    have hn : 1≤(n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    exact ⟨div_pos (half_pos hr) (by positivity),
      (div_le_self (half_pos hr).le hn).trans_lt (by linarith)⟩
  have hseqMem (n : ℕ) : ‖(seq n:ℂ)-(a0:ℂ)‖<r := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    dsimp only [seq]
    rw [add_sub_cancel_left,abs_of_pos (hdelta n).1]
    exact (hdelta n).2
  have hden : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hseq : Tendsto (fun n : ℕ => (seq n:ℂ)) atTop (𝓝 (a0:ℂ)) := by
    have hs : Tendsto seq atTop (𝓝 a0) := by
      convert! (hden.const_div_atTop (r/2)).const_add a0 using 1
      simp only [add_zero]
    exact (Complex.continuous_ofReal.tendsto a0).comp hs
  have hclosure : (a0:ℂ)∈closure ({b : ℂ | incomingBesselCoefficient hR b=
      -besselZeroPhase b*outgoingBesselCoefficient hR b}\{(a0:ℂ)}) := by
    apply mem_closure_of_tendsto hseq (Eventually.of_forall (fun n => ?_))
    refine ⟨real_bessel_connection_phase hR (by dsimp [seq]; linarith [(hdelta n).1])
      (hc _ (hseqMem n)),?_⟩
    simp only [mem_singleton_iff]
    intro he
    have hh := Complex.ofReal_injective he
    dsimp [seq] at hh
    linarith [(hdelta n).1]
  exact (hI.eqOn_of_preconnected_of_mem_closure hO (convex_ball (a0:ℂ) r).isPreconnected
    (hmem.mpr (by simpa only [sub_self,norm_zero] using hr)) hclosure) (hmem.mpr ha)

/-- One genuine common disk carries the original Bessel-Jost canonical phase and a nonzero true outgoing leading coefficient at every complex order.
Use: the original normalized Bessel zero equation may now be divided by its actual analytic outgoing amplitude, retaining the fixed source phase before the complex-frequency zero-tail argument.
Article: jacobi, Lemma E.1.
Proof: choose the actual common quadratic-coefficient half-contraction ray and a positive disk inside the original order half-plane. The actual real phase extends there by the proved identity theorem. A vanishing outgoing factor would force its true incoming counterpart to vanish, contradicting actual Bessel zero simplicity. -/
theorem common_bessel_connection_phase {a0 : ℝ} (ha0 : -1<a0) :
    ∃ R r : ℝ,∃ hR : 0<R,0<r ∧ r<a0+1 ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖<r →
      ‖besselCoefficient a‖/R≤1/2 ∧ -1<a.re ∧
      incomingBesselCoefficient hR a= -besselZeroPhase a*outgoingBesselCoefficient hR a ∧
      outgoingBesselCoefficient hR a≠0 := by
  -- Every analytic and nonvanishing condition is discharged for the original actual coefficient on one common disk.
  obtain ⟨R,hR,hhalf⟩ := common_order_ray (a0:ℂ)
  let r : ℝ := min 1 ((a0+1)/2)
  have hr : 0<r := lt_min (by norm_num) (by linarith)
  have hra : r<a0+1 := (min_le_right 1 ((a0+1)/2)).trans_lt (by linarith)
  have hc (a : ℂ) (ha : ‖a-(a0:ℂ)‖<r) : ‖besselCoefficient a‖/R≤1/2 :=
    hhalf a (ha.le.trans (min_le_left _ _))
  refine ⟨R,r,hR,hr,hra,fun a ha => ⟨hc a ha,?_,?_,?_⟩⟩
  · have hh := Complex.re_le_norm ((a0:ℂ)-a)
    rw [norm_sub_rev] at hh
    simp only [Complex.sub_re,Complex.ofReal_re] at hh
    linarith
  · exact complex_bessel_connection_phase hR hr ha0 hra.le hc ha
  · have hreal : -1<a.re := by
      have hh := Complex.re_le_norm ((a0:ℂ)-a)
      rw [norm_sub_rev] at hh
      simp only [Complex.sub_re,Complex.ofReal_re] at hh
      linarith
    rcases besselConnection_nontrivial hR hreal (hc a ha) with hA | hB
    · exact hA
    · intro hA
      have he := complex_bessel_connection_phase hR hr ha0 hra.le hc ha
      rw [hA,mul_zero] at he
      exact hB he

end
end jacobi.Hankel
