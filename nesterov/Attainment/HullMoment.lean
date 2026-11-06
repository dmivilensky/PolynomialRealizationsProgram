import nesterov.Attainment.NormalizedCertificate
import polyak.Spectral.HullMoment

/-! Complementary slackness for the two-amplitude compact dual hull. The
continuous integration operator is reused verbatim from the Polyak package. -/
noncomputable section
open MeasureTheory Set
open scoped Topology OnePoint
namespace nesterov.Attainment
open Spectral

def dualMomentCLM (lo hi : ℝ) (hlo : 0 < lo) (s : LagParameter lo hi) (C : ℝ) (ν : Spectrum) :
    DualPoint lo hi →L[ℝ] ℝ :=
  (polyak.Spectral.traceIntegralCLM hlo ν).comp (restrictSymbolCLM lo hi s) +
    C • ContinuousLinearMap.fst ℝ ℝ C(LagDomain lo hi,ℂ)

theorem dualMomentCLM_apply (lo hi : ℝ) (hlo : 0 < lo) (s : LagParameter lo hi)
    (C : ℝ) (ν : Spectrum) (d : DualPoint lo hi) :
    dualMomentCLM lo hi hlo s C ν d =
      (∫ c, (d.2 (s,physicalAngle lo hlo c)).re ∂ν) + d.1*C := by
  change (∫ c, (d.2 (s,physicalAngle lo hlo c)).re ∂ν) + C*d.1 = _
  ring

theorem generator_moment_nonneg (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) {ν : Spectrum} {C : ℝ}
    (h : Feasible (polynomialPair u p (σ*s)) s ν C)
    {d : DualPoint lo hi}
    (hd : d ∈ dualGenerators lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)) :
    0 ≤ dualMomentCLM lo hi hlo s C ν d := by
  have hfamily (δ : ℝ) (hδ : δ=1 ∨ δ= -1) (l : OnePoint ℕ) :
      0 ≤ dualMomentCLM lo hi hlo s C ν
        (dualFamily lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) δ l) := by
    rw [dualMomentCLM_apply,dualFamily_charge]
    induction l using OnePoint.rec with
    | infty =>
      simp_rw [dualFamily_physical_infty,Complex.ofReal_re]
      change 0 ≤ meanG ν (polynomialPair u p (σ*s))+δ*C
      have hC := abs_le.mp h.1
      rcases hδ with rfl | rfl <;> nlinarith [hC.1,hC.2]
    | coe n =>
      simp_rw [dualFamily_physical_coe,Complex.ofReal_re]
      rw [integral_div, integral_sub
        (polyak.Spectral.integrable_continuous ν (continuous_lagA _ _ _))
        ((polyak.Spectral.integrable_continuous ν (continuous_lagB _ _)).const_mul δ),
        integral_const_mul]
      change 0 ≤ (meanA ν (polynomialPair u p (σ*s)) s (n+1)-
        δ*meanB ν (polynomialPair u p (σ*s)) (n+1))/Real.sinh ((n+1 : ℕ)*s)+δ*C
      have hs : 0 < Real.sinh ((n+1 : ℕ)*s) := Real.sinh_pos_iff.mpr
        (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) (hlo.trans_le s.property.1))
      have hh := h.2 (n+1) (Nat.succ_pos _)
      apply (mul_nonneg_iff_of_pos_right hs).mp
      rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hs)]
      rcases hδ with rfl | rfl <;> nlinarith [hh.1,hh.2]
  obtain ⟨⟨b,l⟩,rfl⟩ := hd
  exact hfamily _ (by cases b <;> simp) l

theorem dualHull_moment_nonneg (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) {ν : Spectrum} {C : ℝ}
    (h : Feasible (polynomialPair u p (σ*s)) s ν C)
    {d : DualPoint lo hi}
    (hd : d ∈ polynomialDualHull u p lo hi σ hlo) :
    0 ≤ (∫ c, (d.2 (s,physicalAngle lo hlo c)).re ∂ν)+d.1*C := by
  have hh := dualHull_le (-dualMomentCLM lo hi hlo s C ν) 0
    (fun g hg => by simpa using neg_nonpos.mpr (generator_moment_nonneg u p lo hi σ hlo s h hg)) hd
  have hh' : 0 ≤ dualMomentCLM lo hi hlo s C ν d := by simpa using neg_nonpos.mp hh
  rwa [dualMomentCLM_apply] at hh'

theorem dualHull_trace_im_zero (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) {d : DualPoint lo hi} (hd : d ∈ polynomialDualHull u p lo hi σ hlo)
    (c : Frequency) : (d.2 (s,physicalAngle lo hlo c)).im=0 := by
  apply dualHull_eq (imaginaryCLM lo hi s (physicalAngle lo hlo c)) 0 _ hd
  rintro g ⟨⟨b,l⟩,rfl⟩
  change ((dualFamily lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)
    (if b then -1 else 1) l).2 (s,physicalAngle lo hlo c)).im=0
  induction l using OnePoint.rec with
  | infty => rw [dualFamily_physical_infty]; rfl
  | coe n => rw [dualFamily_physical_coe]; rfl

/-- Complementary slackness confines the entire probability measure to the complex zero set. -/
theorem measure_compl_dualZeros_eq_zero (lo hi : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (d : DualPoint lo hi) (ν : Spectrum)
    (hneg : ∀ c, (d.2 (s,physicalAngle lo hlo c)).re ≤ 0)
    (him : ∀ c, (d.2 (s,physicalAngle lo hlo c)).im=0)
    (hmoment : 0 ≤ ∫ c, (d.2 (s,physicalAngle lo hlo c)).re ∂ν) :
    (ν : Measure Frequency) {c | d.2 (s,physicalAngle lo hlo c)=0}ᶜ=0 := by
  let f : Frequency → ℝ := fun c => (d.2 (s,physicalAngle lo hlo c)).re
  have hf : Continuous f := Complex.continuous_re.comp
    (d.2.continuous.comp (continuous_const.prodMk (polyak.Spectral.continuous_dualAngle hlo)))
  have hfi := polyak.Spectral.integrable_continuous ν hf
  have hzero : (∫ c,f c ∂ν)=0 := le_antisymm (integral_nonpos hneg) hmoment
  have hnegzero : (∫ c,-f c ∂ν)=0 := by rw [integral_neg,hzero,neg_zero]
  have hae : ∀ᵐ c ∂(ν : Measure Frequency), -f c=0 :=
    (integral_eq_zero_iff_of_nonneg (fun c => neg_nonneg.mpr (hneg c)) hfi.neg).mp hnegzero
  have hcomplex : ∀ᵐ c ∂(ν : Measure Frequency), d.2 (s,physicalAngle lo hlo c)=0 := by
    filter_upwards [hae] with c hc
    apply Complex.ext
    · change f c=0
      linarith
    · simpa only [Complex.zero_im] using him c
  exact (ae_iff).mp hcomplex

end nesterov.Attainment
