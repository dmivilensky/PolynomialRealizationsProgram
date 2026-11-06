import nesterov.TwoStep.SequenceBridge
import nesterov.TwoStep.Lower
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! The slow ceiling for arbitrary physical parameter filters, via exact stable
real extensions of bad subsequences. No coefficient smoothness is assumed. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def restCoefficientAt (a : A) : ℝ :=
  (1-Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
    (F.tuning a).step_pos.ne' (F.epsilon a^2) 1)/F.epsilon a

def fullCoefficientAt (a : A) : ℝ :=
  (1-Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
    (F.tuning a).step_pos.ne' (F.epsilon a^2) 1)/F.epsilon a

private theorem sequence_rest_ceiling {θ y τ b : ℝ} (F : Scaling ℕ atTop θ y τ)
    (hs : ∀ᶠ n in atTop,(F.tuning n).Stable (F.epsilon n^2) 1) (hb : Flow.cF θ y<b) :
    ∀ᶠ n in atTop,F.restCoefficientAt n≤b := by
  by_contra hn
  have hbad : ∃ᶠ n in atTop,b<F.restCoefficientAt n := by simpa only [not_eventually,not_le] using hn
  obtain ⟨ψ,hψ,hbadψ⟩ := subseq_forall_of_frequently (p:=fun n : ℕ=>b<F.restCoefficientAt n)
    tendsto_id hbad
  let H := F.reindex ψ hψ
  have hHs : ∀ᶠ n in atTop,(H.tuning n).Stable (H.epsilon n^2) 1 := hψ.eventually hs
  obtain ⟨φ,hφ,G,hGe,hmatch,hGs⟩ := H.exists_real_extension hHs (H.limiting_stability_margin_le hHs)
  have hG := G.rest_coefficient_eventually_le hGe hGs hb
  have he := H.epsilon_tendsto.comp hφ.tendsto_atTop
  obtain ⟨n,hn⟩ := (he.eventually hG).exists
  have heq : G.restCoefficient (H.epsilon (φ n))=H.restCoefficientAt (φ n) := by
    unfold restCoefficient restCoefficientAt
    simp only [hmatch n]
  change G.restCoefficient (H.epsilon (φ n))≤b at hn
  rw [heq] at hn
  exact (not_lt_of_ge hn) (hbadψ (φ n))

/-- Quantified slow ceiling for the actual from-rest factor, including real κ-indexed families. -/
theorem rest_coefficient_eventually_le_filter [l.IsCountablyGenerated]
    (hs : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) {b : ℝ} (hb : Flow.cF θ y<b) :
    ∀ᶠ a in l,F.restCoefficientAt a≤b := by
  by_contra hn
  have hbad : ∃ᶠ a in l,b<F.restCoefficientAt a := by simpa only [not_eventually,not_le] using hn
  obtain ⟨s,hsl,hbs⟩ := exists_seq_forall_of_frequently hbad
  let H := F.reindex s hsl
  have hHs : ∀ᶠ n in atTop,(H.tuning n).Stable (H.epsilon n^2) 1 := hsl.eventually hs
  obtain ⟨n,hn⟩ := (sequence_rest_ceiling H hHs hb).exists
  exact (not_lt_of_ge hn) (hbs n)

/-- The full-state factor has the same ceiling because it dominates the rest factor. -/
theorem full_coefficient_eventually_le_filter [l.IsCountablyGenerated]
    (hs : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) {b : ℝ} (hb : Flow.cF θ y<b) :
    ∀ᶠ a in l,F.fullCoefficientAt a≤b := by
  filter_upwards [F.rest_coefficient_eventually_le_filter hs hb,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a ha he he1
  have hμL : F.epsilon a^2<1 := by nlinarith
  have hr := Momentum.restRate_le_momentumRate (β:=(F.tuning a).beta) (τ:=(F.tuning a).tau)
    (F.tuning a).step_pos.ne' (sq_pos_of_pos he) hμL
  have hh := div_le_div_of_nonneg_right (sub_le_sub_left hr 1) he.le
  exact hh.trans ha

end
end nesterov.TwoStep.Scaling
