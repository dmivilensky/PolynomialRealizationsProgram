import nesterov.Momentum.Queries
import nesterov.Rates.RootBounds

/-!
Article: Remark `rem:twostep`, exact from-rest query/iterate rate comparison.
Use: the same actual finite-dimensional executions define both suprema. The
reconstruction pole is retained explicitly and every real limsup is bounded.
-/
namespace nesterov.Momentum
noncomputable section
open Set Filter
open scoped Topology

theorem queryRestEnvelope_le_envelope (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) (n : ℕ) :
    queryRestEnvelope β τ h hh μ L n≤
      (method β τ h hh).queryGain*Real.sqrt (method β τ h hh).memory*
        Rates.envelope (method β τ h hh) μ L n := by
  let M := method β τ h hh
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,_,hr,hz,rfl⟩
  · exact mul_nonneg (mul_nonneg M.queryGain_nonneg (Real.sqrt_nonneg _))
      (Rates.envelope_nonneg M μ L n)
  · have hq := M.norm_query_le r.w n
    have hs := Rates.stateNorm_le_envelope r n
    rw [hr.stateNorm_zero] at hs
    change M.stateNorm r.w n ≤ Rates.envelope M μ L n *
      (Real.sqrt M.memory*‖r.w 0‖) at hs
    apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
    exact hq.trans ((mul_le_mul_of_nonneg_left hs M.queryGain_nonneg).trans_eq (by ring))

theorem query_roots_bounded (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) :
    IsBoundedUnder (·≤·) atTop
      (fun n : ℕ => queryRestEnvelope β τ h hh μ L n^((n:ℝ)⁻¹)) := by
  let M := method β τ h hh
  let C : ℝ := 1+M.queryGain*Real.sqrt M.memory
  have hC : 0<C := by
    dsimp [C]
    linarith [mul_nonneg M.queryGain_nonneg (Real.sqrt_nonneg (M.memory:ℝ))]
  apply Rates.roots_bounded_of_mul_pow (queryRestEnvelope_nonneg β τ h hh μ L) hC (M.stepBound_pos L)
  intro n
  calc
    _ ≤ M.queryGain*Real.sqrt M.memory*Rates.envelope M μ L n :=
      queryRestEnvelope_le_envelope β τ h hh μ L n
    _ ≤ C*Rates.envelope M μ L n := by
      apply mul_le_mul_of_nonneg_right _ (Rates.envelope_nonneg M μ L n)
      dsimp [C]
      linarith
    _ ≤ C*(M.stepBound L)^n :=
      mul_le_mul_of_nonneg_left (Rates.envelope_le M μ L n) hC.le

theorem queryRestRate_nonneg (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) :
    0≤queryRestRate β τ h hh μ L :=
  Rates.root_limsup_nonneg (queryRestEnvelope_nonneg β τ h hh μ L)
    (query_roots_bounded β τ h hh μ L)

/-- The query is a fixed combination of neighboring iterates, with no extra pole. -/
theorem queryRestRate_le_restRate {β τ h μ L : ℝ} (hh : h≠0) (hτ : 0≤τ) :
    queryRestRate β τ h hh μ L≤Rates.restRate (method β τ h hh) μ L := by
  apply Rates.neighbor_root_limsup_le (a:=1+τ) (b:=τ) (queryRestEnvelope_nonneg β τ h hh μ L)
    (Rates.restEnvelope_nonneg (method β τ h hh) μ L)
    (Rates.rest_roots_bounded (method β τ h hh) μ L) (by linarith) hτ
    (queryRestEnvelope_zero_le_one β τ h hh μ L)
  exact queryRestEnvelope_succ_le hh hτ

/-- Inverting the query adds at most the exact stable pole τ/(1+τ). -/
theorem restRate_le_max_queryRestRate {β τ h μ L : ℝ} (hh : h≠0) (hτ : 0≤τ) :
    Rates.restRate (method β τ h hh) μ L≤max (queryRestRate β τ h hh μ L) (queryPole τ) := by
  apply Rates.filter_root_limsup_le_max (queryRestEnvelope_nonneg β τ h hh μ L)
    (Rates.restEnvelope_nonneg (method β τ h hh) μ L)
    (query_roots_bounded β τ h hh μ L) (queryPole_mem hτ).1
    (restEnvelope_zero_le_one (method β τ h hh) μ L)
  exact restEnvelope_succ_le_query hh hτ

/-- The source's complete query/iterate sandwich, with the initialization fixed. -/
theorem query_rest_rate_sandwich {β τ h μ L : ℝ} (hh : h≠0) (hτ : 0≤τ) :
    queryRestRate β τ h hh μ L≤momentumRestRate β τ h hh μ L ∧
    momentumRestRate β τ h hh μ L≤max (queryRestRate β τ h hh μ L) (queryPole τ) :=
  ⟨queryRestRate_le_restRate hh hτ,restRate_le_max_queryRestRate hh hτ⟩

theorem queryRestRate_eq_restRate_of_pole_lt_query {β τ h μ L : ℝ} (hh : h≠0) (hτ : 0≤τ)
    (hp : queryPole τ<queryRestRate β τ h hh μ L) :
    queryRestRate β τ h hh μ L=momentumRestRate β τ h hh μ L := by
  apply le_antisymm (queryRestRate_le_restRate hh hτ)
  have hh' := restRate_le_max_queryRestRate (μ:=μ) (L:=L) (β:=β) hh hτ
  rwa [max_eq_left hp.le] at hh'

theorem queryRestRate_eq_restRate_of_pole_lt_rest {β τ h μ L : ℝ} (hh : h≠0) (hτ : 0≤τ)
    (hp : queryPole τ<momentumRestRate β τ h hh μ L) :
    queryRestRate β τ h hh μ L=momentumRestRate β τ h hh μ L := by
  apply le_antisymm (queryRestRate_le_restRate hh hτ)
  have hh' := restRate_le_max_queryRestRate (μ:=μ) (L:=L) (β:=β) hh hτ
  rcases le_max_iff.mp hh' with hq | hq
  · exact hq
  · exact False.elim (not_le_of_gt hp hq)

/-- The reconstruction pole is monotone on the source extrapolation domain. -/
theorem queryPole_mono {a b : ℝ} (ha : 0≤a) (hab : a≤b) : queryPole a≤queryPole b := by
  unfold queryPole
  apply (div_le_div_iff₀ (by linarith : 0<1+a) (by linarith : 0<1+b)).mpr
  nlinarith

/-- In any family with bounded nonnegative extrapolation and a rest factor
converging to one, query and iterate factors agree eventually. -/
theorem eventually_queryRate_eq_of_rest_tendsto_one {ι : Type*} {l : Filter ι}
    (β τ h μ L : ι → ℝ) (hh : ∀ i,h i≠0) {B : ℝ} (hB : 0≤B)
    (hτ : ∀ᶠ i in l,0≤τ i ∧ τ i≤B)
    (hr : Tendsto (fun i => momentumRestRate (β i) (τ i) (h i) (hh i) (μ i) (L i)) l (𝓝 1)) :
    ∀ᶠ i in l, queryRestRate (β i) (τ i) (h i) (hh i) (μ i) (L i)=
      momentumRestRate (β i) (τ i) (h i) (hh i) (μ i) (L i) := by
  have hp : queryPole B<1 := (queryPole_mem hB).2
  filter_upwards [hτ,hr.eventually (lt_mem_nhds hp)] with i hi hrate
  exact queryRestRate_eq_restRate_of_pole_lt_rest (hh i) hi.1
    ((queryPole_mono hi.1 hi.2).trans_lt hrate)

/-- The symmetric version uses convergence of the actual query factor. -/
theorem eventually_queryRate_eq_of_query_tendsto_one {ι : Type*} {l : Filter ι}
    (β τ h μ L : ι → ℝ) (hh : ∀ i,h i≠0) {B : ℝ} (hB : 0≤B)
    (hτ : ∀ᶠ i in l,0≤τ i ∧ τ i≤B)
    (hr : Tendsto (fun i => queryRestRate (β i) (τ i) (h i) (hh i) (μ i) (L i)) l (𝓝 1)) :
    ∀ᶠ i in l, queryRestRate (β i) (τ i) (h i) (hh i) (μ i) (L i)=
      momentumRestRate (β i) (τ i) (h i) (hh i) (μ i) (L i) := by
  have hp : queryPole B<1 := (queryPole_mem hB).2
  filter_upwards [hτ,hr.eventually (lt_mem_nhds hp)] with i hi hrate
  exact queryRestRate_eq_restRate_of_pole_lt_query (hh i) hi.1
    ((queryPole_mono hi.1 hi.2).trans_lt hrate)

end
end nesterov.Momentum
