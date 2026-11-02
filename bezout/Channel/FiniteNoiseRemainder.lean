import bezout.Channel.FiniteNoiseVariance
import Mathlib.Analysis.Asymptotics.Defs

/-!
Article: bezout, Equation `eq:experiment-finite-variance`, fixed-horizon remainder.
Use: separates the exact singleton variance from the nonnegative higher orders
and proves a genuine O(delta^4) bound with an explicit finite coefficient.
Proof: partition insertion masks by cardinality and use squared powers of delta.
-/

namespace bezout.Channel
noncomputable section
open Polynomial MeasureTheory Filter Topology
open scoped BigOperators
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact sum of all physical variance orders containing at least two calls. -/
def finiteNoiseRemainder (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) : ℝ :=
  ∑ S ∈ (Finset.range N).powerset.filter (fun S => 2≤S.card),
    δ^(2*S.card)*‖finiteNoiseCoefficient h H P initial S‖^2

/-- An explicit finite constant for the fixed-horizon fourth-order remainder. -/
def finiteNoiseRemainderConstant (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) : ℝ :=
  ∑ S ∈ (Finset.range N).powerset.filter (fun S => 2≤S.card),
    ‖finiteNoiseCoefficient h H P initial S‖^2

/-- The full actual variance is its singleton contribution plus the exact higher-order sum. -/
theorem finiteSignOutput_variance_split (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) :
    (∫ ω, ‖finiteSignOutput h H P initial δ ω-(aeval H h.terminal) initial‖^2
      ∂bezout.Probability.Signs.law N)=
      δ^2*(∑ s : Fin N, ‖finiteNoiseCoefficient h H P initial {s.val}‖^2)+
        finiteNoiseRemainder h H P initial δ := by
  have hpart : (Finset.range N).powerset.erase ∅=
      Finset.powersetCard 1 (Finset.range N) ∪
      (Finset.range N).powerset.filter (fun S => 2≤S.card) := by
    apply Finset.ext
    intro S
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_powersetCard,
      Finset.mem_filter, Finset.mem_powerset]
    have hz : S.card=0 ↔ S=∅ := Finset.card_eq_zero
    by_cases hsub : S⊆Finset.range N
    · simp only [hsub, and_true, true_and]
      have hz' : S ≠ ∅ ↔ S.card ≠ 0 := not_congr hz.symm
      rw [hz']
      omega
    · simp [hsub]
  have hd : Disjoint (Finset.powersetCard 1 (Finset.range N))
      ((Finset.range N).powerset.filter (fun S => 2≤S.card)) := by
    apply Finset.disjoint_left.mpr
    intro S h1 h2
    have ha := (Finset.mem_powersetCard.mp h1).2
    have hb := (Finset.mem_filter.mp h2).2
    omega
  rw [finiteSignOutput_variance, hpart, Finset.sum_union hd]
  have hs : (∑ S ∈ Finset.powersetCard 1 (Finset.range N),
      δ^(2*S.card)*‖finiteNoiseCoefficient h H P initial S‖^2)=
      δ^2*(∑ s : Fin N, ‖finiteNoiseCoefficient h H P initial {s.val}‖^2) := by
    rw [Finset.powersetCard_one, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, Finset.card_singleton, Nat.mul_one]
    rw [← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
      (fun s => ‖finiteNoiseCoefficient h H P initial {s}‖^2) N]
  rw [hs]
  rfl

/-- Higher finite-noise orders contribute nonnegative variance at every noise size. -/
theorem finiteNoiseRemainder_nonneg (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) :
    0≤finiteNoiseRemainder h H P initial δ := by
  apply Finset.sum_nonneg
  intro S _
  apply mul_nonneg _ (sq_nonneg _)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg δ) S.card

/-- The explicit fixed-horizon remainder coefficient is nonnegative. -/
theorem finiteNoiseRemainderConstant_nonneg (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) :
    0≤finiteNoiseRemainderConstant h H P initial := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- A uniform fourth-order estimate holds throughout the unit noise neighborhood. -/
theorem finiteNoiseRemainder_le (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) (hδ : |δ|≤1) :
    finiteNoiseRemainder h H P initial δ≤δ^4*finiteNoiseRemainderConstant h H P initial := by
  have hδsq : δ^2≤1 := by
    have hh := pow_le_pow_left₀ (abs_nonneg δ) hδ 2
    simpa only [sq_abs, one_pow] using hh
  unfold finiteNoiseRemainder finiteNoiseRemainderConstant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hc := (Finset.mem_filter.mp hS).2
  have hp : δ^(2*S.card)≤δ^4 := by
    have hh := pow_le_pow_of_le_one (sq_nonneg δ) hδsq hc
    simpa only [← pow_mul, show 2*2=4 by omega] using hh
  exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)

/-- The nonnegative exact remainder is genuinely O(delta^4) at fixed horizon. -/
theorem finiteNoiseRemainder_isBigO (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) :
    Asymptotics.IsBigOWith (finiteNoiseRemainderConstant h H P initial) (𝓝 (0:ℝ))
      (finiteNoiseRemainder h H P initial) (fun δ => δ^4) := by
  apply Asymptotics.isBigOWith_iff.mpr
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with δ hδ
  have ha : |δ|≤1 := abs_le.mpr ⟨hδ.1.le,hδ.2.le⟩
  simp only [Real.norm_eq_abs, abs_of_nonneg (finiteNoiseRemainder_nonneg h H P initial δ),
    abs_of_nonneg (by positivity : (0:ℝ)≤δ^4)]
  exact (finiteNoiseRemainder_le h H P initial δ ha).trans_eq (mul_comm _ _)

end
end bezout.Channel
