import nesterov.Smooth.Rest
import nesterov.Rates.Limit
import nesterov.Rates.RootBounds

/-!
Article: Definition `def:rate` and Lemma `lem:envelope`.
Use: the literal finite-dimensional from-rest limsup is bounded by the
all-Hilbert free-state limit. The fixed factor √D disappears under nth roots.
-/
namespace nesterov.Rates
noncomputable section
open Filter
open scoped Topology
variable (M : StationaryMethod)

/-- The source limsup of finite-dimensional from-rest suprema. -/
def restRate (μ L : ℝ) : ℝ :=
  limsup (fun n : ℕ => restEnvelope M μ L n ^ ((n:ℝ)⁻¹)) atTop

/-- Every root sequence in the literal rest-rate limsup is bounded. -/
theorem rest_roots_bounded (μ L : ℝ) :
    IsBoundedUnder (·≤·) atTop (fun n : ℕ => restEnvelope M μ L n^((n:ℝ)⁻¹)) := by
  apply roots_bounded_of_mul_pow (restEnvelope_nonneg M μ L)
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr M.memory_pos)) (M.stepBound_pos L)
  intro n
  exact (restEnvelope_le_envelope M μ L n).trans
    (mul_le_mul_of_nonneg_left (envelope_le M μ L n) (Real.sqrt_nonneg _))

theorem restRate_nonneg (μ L : ℝ) : 0≤restRate M μ L :=
  root_limsup_nonneg (restEnvelope_nonneg M μ L) (rest_roots_bounded M μ L)

/-- The complete initial memory contributes only a horizon-independent factor. -/
theorem restRate_le_rate {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    restRate M μ L ≤ rate M μ L := by
  have hinv : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfactor : Tendsto (fun n : ℕ => (Real.sqrt M.memory)^((n:ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero,Function.comp_def] using
      (Real.continuousAt_const_rpow (a:=Real.sqrt M.memory) (b:=0)
        (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr M.memory_pos)))).tendsto.comp hinv
  have hlim := hfactor.mul (tendsto_envelope_root M hμ hμL)
  simp only [one_mul] at hlim
  have hpoint (n : ℕ) : restEnvelope M μ L n^((n:ℝ)⁻¹) ≤
      (Real.sqrt M.memory)^((n:ℝ)⁻¹)*envelope M μ L n^((n:ℝ)⁻¹) := by
    calc
      _ ≤ (Real.sqrt M.memory*envelope M μ L n)^((n:ℝ)⁻¹) :=
        Real.rpow_le_rpow (restEnvelope_nonneg M μ L n) (restEnvelope_le_envelope M μ L n)
          (by positivity)
      _ = _ := Real.mul_rpow (Real.sqrt_nonneg _) (envelope_nonneg M μ L n)
  have hh := limsup_le_limsup (Eventually.of_forall hpoint)
    (isCoboundedUnder_le_of_le atTop (fun n =>
      Real.rpow_nonneg (restEnvelope_nonneg M μ L n) _)) hlim.isBoundedUnder_le
  rwa [hlim.limsup_eq] at hh

/-- The C∞ restriction leaves the from-rest asymptotic factor unchanged. -/
theorem smooth_restRate_eq (μ L : ℝ) :
    limsup (fun n : ℕ => smoothRestEnvelope M μ L n^((n:ℝ)⁻¹)) atTop=restRate M μ L := by
  simp only [smoothRestEnvelope_eq_restEnvelope,restRate]

/-- The C∞ finite-dimensional envelope has the same uniform root limit. -/
theorem tendsto_smoothEnvelope_root {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    Tendsto (fun n : ℕ => smoothEnvelope M μ L n^((n:ℝ)⁻¹)) atTop (𝓝 (rate M μ L)) := by
  simpa only [smoothEnvelope_eq_envelope] using tendsto_envelope_root M hμ hμL

end
end nesterov.Rates
