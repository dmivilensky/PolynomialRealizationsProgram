import polyak.Spectral.LimitingDual
import polyak.Spectral.HullZeros
import polyak.Spectral.HullMoment

/-!
Article: Appendix A, finite-support lemma, every optimal measure.
Use: one limiting analytic symbol confines all feasible boundary measures to
one finite interior zero set, with no atomicity assumption on those measures.
Proof: complementary slackness follows from the closed convex moment inequality;
the negative continuous symbol has integral zero and therefore vanishes almost everywhere.
-/

namespace polyak.Spectral
noncomputable section
open MeasureTheory Set

/-- Article: complementary slackness confines the whole measure to the actual complex zero set. -/
theorem measure_compl_dualZeros_eq_zero {s : ℝ} (hs : 0 < s) (u : ℝ)
    (d : DualCoefficient s) (ν : Spectrum)
    (hneg : ∀ c : Frequency,(evaluateDual u d (dualAngle s hs c)).re ≤ 0)
    (him : ∀ c : Frequency,(evaluateDual u d (dualAngle s hs c)).im=0)
    (hmoment : 0 ≤ avg ν (fun c => (evaluateDual u d (dualAngle s hs c)).re)) :
    (ν : Measure Frequency) (dualZeros hs u d)ᶜ=0 := by
  let f : Frequency → ℝ := fun c => (evaluateDual u d (dualAngle s hs c)).re
  have hangle : Continuous (dualAngle s hs) := by unfold dualAngle; fun_prop
  have hf : Continuous f := Complex.continuous_re.comp ((evaluateDual u d).continuous.comp hangle)
  have hfi := integrable_continuous ν hf
  have hzero : (∫ c,f c ∂ν)=0 := le_antisymm (integral_nonpos hneg) hmoment
  have hnegzero : (∫ c,-f c ∂ν)=0 := by rw [integral_neg,hzero,neg_zero]
  have hae : ∀ᵐ c ∂(ν : Measure Frequency),-f c=0 :=
    (integral_eq_zero_iff_of_nonneg (fun c => neg_nonneg.mpr (hneg c)) hfi.neg).mp hnegzero
  have hcomplex : ∀ᵐ c ∂(ν : Measure Frequency),evaluateDual u d (dualAngle s hs c)=0 := by
    filter_upwards [hae] with c hc
    apply Complex.ext
    · change f c=0
      linarith
    · simpa only [Complex.zero_im] using him c
  exact (ae_iff).mp hcomplex

/-- Article: every boundary measure has finite support strictly inside (-1,1).
Use: the common finite carrier is proved before choosing any optimal measure or finite realization. -/
theorem exists_finite_boundary_carrier {s : ℝ} (hs : 0 < s) (hV : 0 < V s) :
    ∃ F : Set Frequency,F.Finite ∧ (∀ c∈F,-1<(c : ℝ) ∧ (c : ℝ)<1) ∧
      ∀ (ν : Spectrum) (C : ℝ),Feasible (V s) s ν C → (ν : Measure Frequency) Fᶜ=0 := by
  obtain ⟨d,hd,hcharge,hneg⟩ := exists_limiting_dual hs
  have hu : 0 < Real.sinh (V s) := Real.sinh_pos_iff.mpr hV
  refine ⟨dualZeros hs (Real.sinh (V s)) d,dualZeros_finite hs hu hd,
    fun c hc => dualZeros_interior hs hu hd hc,fun ν C h => ?_⟩
  have hm := dualHull_moment_nonneg hs h hd
  rw [hcharge,zero_mul,add_zero] at hm
  exact measure_compl_dualZeros_eq_zero hs _ d ν hneg (dualHull_trace_im_zero hs _ hd) hm

end
end polyak.Spectral
