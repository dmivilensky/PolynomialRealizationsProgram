import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
Article: bezout, Equation (8), Theorem 3.1 and Appendix B (martingale noise).
Use: deterministic physical response operators preserve conditional centering,
and their terminal mean-square error is the exact sum of the individual energies.
Proof: the conditional-expectation pull-out identity gives orthogonality to the
past; the finite Pythagorean identity then removes every cross term.
-/

namespace bezout.Probability

open MeasureTheory Filter
open scoped BigOperators
noncomputable section

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- Two square-integrable Hilbert-valued functions have an integrable inner
product. Article: bezout, Appendix B. Use: justify the pull-out and sum integrals.
Proof: polarization expresses the product using three integrable squared norms. -/
theorem integrable_inner_of_memLp {f g : Ω → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => inner ℝ (f ω) (g ω)) μ := by
  have hsum := (hf.add hg).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hleft := hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hright := hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  apply (((hsum.sub hleft).sub hright).div_const 2).congr
  exact Eventually.of_forall fun ω => by
    simp only [Pi.add_apply, Pi.sub_apply, norm_add_sq_real]
    ring

/-- A conditionally centered error is orthogonal in expectation to any
square-integrable vector measurable before its call. Article: bezout, Appendix B.
Use: physical martingale errors at distinct times have zero cross covariance. -/
theorem integral_inner_eq_zero_of_condExp {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f g : Ω → E}
    (hf : StronglyMeasurable[m] f) (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hg : μ[g | m] =ᵐ[μ] 0) :
    ∫ ω, inner ℝ (f ω) (g ω) ∂μ = 0 := by
  have hpull := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hf
    (integrable_inner_of_memLp hf2 hg2) (hg2.integrable (by norm_num))
  change μ[fun ω => inner ℝ (f ω) (g ω) | m] =ᵐ[μ]
    (fun ω => inner ℝ (f ω) (μ[g | m] ω)) at hpull
  calc
    _ = ∫ ω, μ[fun ω => inner ℝ (f ω) (g ω) | m] ω ∂μ :=
      (integral_condExp hm).symm
    _ = 0 := by
      have hzero : μ[fun ω => inner ℝ (f ω) (g ω) | m] =ᵐ[μ] 0 := by
        filter_upwards [hpull, hg] with ω hp hz
        simpa [hz] using hp
      exact (integral_congr_ae hzero).trans (by simp)

/-- The finite martingale-difference assumptions of the actual oracle model.
Article: bezout, Equation (8). The error at call s is measurable at s+1 and
centered conditional on s; no independence between different calls is assumed.
Use: exact terminal MSE for deterministic physical response operators. -/
structure MartingaleDifferences (N : ℕ) (𝓕 : Filtration ℕ mΩ) (w : ℕ → Ω → E)
    (μ : Measure Ω) : Prop where
  adapted : ∀ s, s < N → StronglyMeasurable[𝓕 (s + 1)] (w s)
  squareIntegrable : ∀ s, s < N → MemLp (w s) 2 μ
  centered : ∀ s, s < N → μ[w s | 𝓕 s] =ᵐ[μ] 0

namespace MartingaleDifferences

variable {N : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
  (hw : MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ]

include hw

/-- Conditional centering implies zero unconditional mean.
Article: bezout, Appendix B. Use: the nominal terminal has no noise-bias term. -/
theorem integral_eq_zero (s : ℕ) (hs : s < N) : ∫ ω, w s ω ∂μ = 0 := by
  calc
    _ = ∫ ω, μ[w s | 𝓕 s] ω ∂μ := (integral_condExp (𝓕.le s)).symm
    _ = 0 := (integral_congr_ae (hw.centered s hs)).trans (by simp)

/-- Distinct oracle errors are orthogonal in expectation.
Article: bezout, Appendix B. Use: the exact additive martingale MSE identity. -/
theorem integral_inner_eq_zero (s t : ℕ) (hs : s < N) (ht : t < N) (hst : s < t) :
    ∫ ω, inner ℝ (w s ω) (w t ω) ∂μ = 0 :=
  integral_inner_eq_zero_of_condExp (𝓕.le t)
    ((hw.adapted s hs).mono (𝓕.mono (by omega)))
    (hw.squareIntegrable s hs) (hw.squareIntegrable t ht) (hw.centered t ht)

/-- A deterministic continuous linear response preserves all martingale
difference assumptions. Article: bezout, Appendix B. Use: apply the MSE identity
to the physical transfers Φ_s(H), rather than to internal recurrence residuals. -/
theorem map (L : ℕ → E →L[ℝ] F) :
    MartingaleDifferences N 𝓕 (fun s ω => L s (w s ω)) μ where
  adapted s hs := (L s).continuous.comp_stronglyMeasurable (hw.adapted s hs)
  squareIntegrable s hs := (hw.squareIntegrable s hs).continuousLinearMap_comp (L s)
  centered s hs := by
    have hcomm := (L s).comp_condExp_comm
      ((hw.squareIntegrable s hs).integrable (by norm_num)) (m := 𝓕 s)
    change (fun ω => L s (μ[w s | 𝓕 s] ω)) =ᵐ[μ]
      μ[fun ω => L s (w s ω) | 𝓕 s] at hcomm
    filter_upwards [hcomm, hw.centered s hs] with ω hc hz
    simpa [Function.comp_apply, hz] using hc.symm

omit [CompleteSpace E] in
/-- The partial noise sum is square integrable.
Article: bezout, Appendix B. Use: every finite norm-square expansion is integrable. -/
theorem memLp_sum (n : ℕ) (hn : n ≤ N) :
    MemLp (fun ω => ∑ s ∈ Finset.range n, w s ω) 2 μ := by
  induction n with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty] using
      (memLp_const (μ := μ) (p := 2) (0 : E))
  | succ n ih =>
    have heq : (fun ω => ∑ s ∈ Finset.range (n + 1), w s ω) =
        ((fun ω => ∑ s ∈ Finset.range n, w s ω) + w n) := by
      funext ω
      exact Finset.sum_range_succ _ _
    rw [heq]
    exact (ih (by omega)).add (hw.squareIntegrable n (by omega))

/-- Exact finite-horizon MSE of a deterministic bias plus martingale differences.
Article: bezout, Theorem 3.1 and Appendix B. Use: after applying `map`, this is
the article's identity with arbitrary deterministic physical response operators. -/
theorem integral_norm_sq_sum (v : E) :
    ∫ ω, ‖v + ∑ s ∈ Finset.range N, w s ω‖ ^ 2 ∂μ =
      ‖v‖ ^ 2 + ∑ s ∈ Finset.range N, ∫ ω, ‖w s ω‖ ^ 2 ∂μ := by
  have hprefix : ∀ n, n ≤ N →
      (∫ ω, ‖v + ∑ s ∈ Finset.range n, w s ω‖ ^ 2 ∂μ) =
        ‖v‖ ^ 2 + ∑ s ∈ Finset.range n, ∫ ω, ‖w s ω‖ ^ 2 ∂μ := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h2 := (hw.squareIntegrable n (by omega))
      have hleft : MemLp (fun ω => v + ∑ s ∈ Finset.range n, w s ω) 2 μ :=
        (memLp_const (μ := μ) (p := 2) v).add (hw.memLp_sum n (by omega))
      have hcross : (∫ ω, inner ℝ (v + ∑ s ∈ Finset.range n, w s ω) (w n ω) ∂μ) = 0 := by
        have hmeas : StronglyMeasurable[𝓕 n] (fun ω => v + ∑ s ∈ Finset.range n, w s ω) := by
          apply stronglyMeasurable_const.add
          apply Finset.stronglyMeasurable_fun_sum (Finset.range n)
          intro s hs
          have hsn : s < n := Finset.mem_range.mp hs
          exact (hw.adapted s (by omega)).mono
            (𝓕.mono (show s + 1 ≤ n by omega))
        exact integral_inner_eq_zero_of_condExp (𝓕.le n) hmeas hleft h2 (hw.centered n (by omega))
      rw [show (fun ω => ‖v + ∑ s ∈ Finset.range (n + 1), w s ω‖ ^ 2) =
          (fun ω => ‖v + ∑ s ∈ Finset.range n, w s ω‖ ^ 2 +
            2 * inner ℝ (v + ∑ s ∈ Finset.range n, w s ω) (w n ω) +
            ‖w n ω‖ ^ 2) from by
        funext ω
        rw [Finset.sum_range_succ, ← add_assoc, norm_add_sq_real]]
      have hleftint : Integrable (fun ω => ‖v + ∑ s ∈ Finset.range n, w s ω‖ ^ 2) μ :=
        hleft.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      have hrightint : Integrable (fun ω => ‖w n ω‖ ^ 2) μ :=
        h2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      have hcrossint : Integrable (fun ω =>
          2 * inner ℝ (v + ∑ s ∈ Finset.range n, w s ω) (w n ω)) μ :=
        (integrable_inner_of_memLp hleft h2).const_mul 2
      have hsplit := integral_add (hleftint.add hcrossint) hrightint
      simp only [Pi.add_apply] at hsplit
      rw [hsplit]
      rw [integral_add hleftint hcrossint, integral_const_mul, hcross]
      simp only [mul_zero, add_zero]
      rw [ih (by omega), Finset.sum_range_succ]
      ring
  exact hprefix N le_rfl

/-- Exact MSE after arbitrary fixed continuous linear physical responses.
Article: bezout, Appendix B. Use: instantiate L_s=Φ_s(H) and v=p_N(H)e₀. -/
theorem integral_norm_sq_response (v : F) (L : ℕ → E →L[ℝ] F) :
    ∫ ω, ‖v + ∑ s ∈ Finset.range N, L s (w s ω)‖ ^ 2 ∂μ =
      ‖v‖ ^ 2 + ∑ s ∈ Finset.range N, ∫ ω, ‖L s (w s ω)‖ ^ 2 ∂μ :=
  (hw.map L).integral_norm_sq_sum v

end MartingaleDifferences
end
end bezout.Probability
