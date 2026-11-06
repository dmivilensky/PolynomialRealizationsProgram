import nesterov.Momentum.Rates
import nesterov.Rates.Rest

/-!
Article: `rem:twostep`, the rates of iterates and queries from rest.
Use: literal query suprema over the same actual finite-dimensional objectives,
and finite-horizon inequalities before taking any asymptotic rate.
-/
namespace nesterov.Momentum
noncomputable section
open Set Filter
open scoped Topology

def queryRestRatios (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : Rates.HilbertRun (method β τ h hh) μ L,
    ∃ _ : FiniteDimensional ℝ r.Carrier,
    r.FromRest ∧ r.w 0≠0 ∧
      x=‖(method β τ h hh).query r.w n‖/‖r.w 0‖}

def queryRestEnvelope (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (queryRestRatios β τ h hh μ L n))

def queryRestRate (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) : ℝ :=
  limsup (fun n : ℕ => queryRestEnvelope β τ h hh μ L n^((n:ℝ)⁻¹)) atTop

theorem queryRestRatios_bddAbove (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) (n : ℕ) :
    BddAbove (insert 0 (queryRestRatios β τ h hh μ L n)) := by
  let M := method β τ h hh
  refine ⟨M.queryGain*Real.sqrt M.memory*Rates.envelope M μ L n, ?_⟩
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

theorem queryRestEnvelope_nonneg (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) (n : ℕ) :
    0≤queryRestEnvelope β τ h hh μ L n :=
  le_csSup (queryRestRatios_bddAbove β τ h hh μ L n) (mem_insert _ _)

theorem query_ratio_le {β τ h μ L : ℝ} (hh : h≠0)
    (r : Rates.HilbertRun (method β τ h hh) μ L) [FiniteDimensional ℝ r.Carrier]
    (hr : r.FromRest) (hz : r.w 0≠0) (n : ℕ) :
    ‖(method β τ h hh).query r.w n‖/‖r.w 0‖≤queryRestEnvelope β τ h hh μ L n :=
  le_csSup (queryRestRatios_bddAbove β τ h hh μ L n)
    (mem_insert_of_mem _ ⟨r,inferInstance,hr,hz,rfl⟩)

theorem rest_ratio_le {M : StationaryMethod} {μ L : ℝ}
    (r : Rates.HilbertRun M μ L) [FiniteDimensional ℝ r.Carrier]
    (hr : r.FromRest) (hz : r.w 0≠0) (n : ℕ) :
    ‖r.w (n+M.memory-1)‖/‖r.w 0‖≤Rates.restEnvelope M μ L n :=
  le_csSup (Rates.restRatios_bddAbove M μ L n)
    (mem_insert_of_mem _ ⟨r,inferInstance,hr,hz,rfl⟩)

theorem queryRestEnvelope_zero_le_one (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) :
    queryRestEnvelope β τ h hh μ L 0≤1 := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,_,hr,hz,rfl⟩
  · norm_num
  · have hi : r.w 1=r.w 0 := hr (1 : Fin 2)
    rw [method_query]
    simp [hi, norm_ne_zero_iff.mpr hz]

theorem restEnvelope_zero_le_one (M : StationaryMethod) (μ L : ℝ) :
    Rates.restEnvelope M μ L 0≤1 := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,_,hr,hz,rfl⟩
  · norm_num
  · have hi := hr (⟨M.memory-1,by have := M.memory_pos; omega⟩ : Fin M.memory)
    simp only [Nat.zero_add]
    rw [hi, div_self (norm_ne_zero_iff.mpr hz)]

/-- The direct finite-horizon query estimate keeps both neighboring iterates. -/
theorem queryRestEnvelope_succ_le {β τ h μ L : ℝ} (hh : h≠0) (hτ : 0≤τ) (n : ℕ) :
    queryRestEnvelope β τ h hh μ L (n+1)≤
      (1+τ)*Rates.restEnvelope (method β τ h hh) μ L (n+1)+
      τ*Rates.restEnvelope (method β τ h hh) μ L n := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,hfd,hr,hz,rfl⟩
  · exact add_nonneg (mul_nonneg (by linarith) (Rates.restEnvelope_nonneg _ _ _ _))
      (mul_nonneg hτ (Rates.restEnvelope_nonneg _ _ _ _))
  · let _ : FiniteDimensional ℝ r.Carrier := hfd
    have ha := rest_ratio_le r hr hz (n+1)
    have hb := rest_ratio_le r hr hz n
    change ‖r.w (n+2)‖/‖r.w 0‖≤Rates.restEnvelope (method β τ h hh) μ L (n+1) at ha
    change ‖r.w (n+1)‖/‖r.w 0‖≤Rates.restEnvelope (method β τ h hh) μ L n at hb
    have hq : ‖(method β τ h hh).query r.w (n+1)‖≤
        (1+τ)*‖r.w (n+2)‖+τ*‖r.w (n+1)‖ := by
      rw [method_query]
      have he : r.w (n+1+1)+τ • (r.w (n+1+1)-r.w (n+1)) =
          (1+τ) • r.w (n+2)-τ • r.w (n+1) := by
        module
      rw [he]
      exact (norm_sub_le _ _).trans (by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ,
          abs_of_nonneg (show 0≤1+τ by linarith),le_refl])
    apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
    have ha' := (div_le_iff₀ (norm_pos_iff.mpr hz)).mp ha
    have hb' := (div_le_iff₀ (norm_pos_iff.mpr hz)).mp hb
    nlinarith

def queryPole (τ : ℝ) : ℝ := τ/(1+τ)

theorem queryPole_mem {τ : ℝ} (hτ : 0≤τ) :
    0≤queryPole τ ∧ queryPole τ<1 := by
  have hp : 0<1+τ := by linarith
  exact ⟨div_nonneg hτ hp.le,(div_lt_one hp).mpr (by linarith)⟩

/-- Exact inversion at one step; no oracle or trajectory assumption is involved. -/
theorem inverse_query {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : ℝ) (hτ : 1+τ≠0) (a b : E) :
    b=(1/(1+τ)) • (b+τ • (b-a))+queryPole τ • a := by
  have he : b+τ • (b-a)=(1+τ) • b-τ • a := by module
  rw [he,smul_sub,smul_smul,one_div,inv_mul_cancel₀ hτ,one_smul]
  dsimp [queryPole]
  module

/-- Recovering iterates from queries is a stable first-order filter. The
slightly relaxed coefficient 1 is useful for uniform geometric majorants. -/
theorem restEnvelope_succ_le_query {β τ h μ L : ℝ} (hh : h≠0) (hτ : 0≤τ) (n : ℕ) :
    Rates.restEnvelope (method β τ h hh) μ L (n+1)≤
      queryRestEnvelope β τ h hh μ L (n+1)+
      queryPole τ*Rates.restEnvelope (method β τ h hh) μ L n := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,hfd,hr,hz,rfl⟩
  · exact add_nonneg (queryRestEnvelope_nonneg _ _ _ _ _ _ _)
      (mul_nonneg (queryPole_mem hτ).1 (Rates.restEnvelope_nonneg _ _ _ _))
  · let _ : FiniteDimensional ℝ r.Carrier := hfd
    have hq := query_ratio_le hh r hr hz (n+1)
    have hb := rest_ratio_le r hr hz n
    change ‖r.w (n+1)‖/‖r.w 0‖≤Rates.restEnvelope (method β τ h hh) μ L n at hb
    change ‖r.w (n+2)‖/‖r.w 0‖≤_
    have hp : 0<1+τ := by linarith
    have hi := inverse_query τ (ne_of_gt hp) (r.w (n+1)) (r.w (n+2))
    have hinv : 0≤1/(1+τ) := by positivity
    have hinv1 : 1/(1+τ)≤1 := (div_le_one hp).mpr (by linarith)
    have hn : ‖r.w (n+2)‖≤‖(method β τ h hh).query r.w (n+1)‖+
        queryPole τ*‖r.w (n+1)‖ := by
      calc
        _ = ‖(1/(1+τ)) • (method β τ h hh).query r.w (n+1)+
            queryPole τ • r.w (n+1)‖ := by
          congr 1
          simpa only [method_query,show n+1+1=n+2 by omega] using hi
        _ ≤ ‖(1/(1+τ)) • (method β τ h hh).query r.w (n+1)‖+
            ‖queryPole τ • r.w (n+1)‖ := norm_add_le _ _
        _ ≤ _ := by
          simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hinv,
            abs_of_nonneg (queryPole_mem hτ).1]
          nlinarith [norm_nonneg ((method β τ h hh).query r.w (n+1))]
    apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
    have hq' := (div_le_iff₀ (norm_pos_iff.mpr hz)).mp hq
    have hb' := (div_le_iff₀ (norm_pos_iff.mpr hz)).mp hb
    nlinarith [(queryPole_mem hτ).1]

end
end nesterov.Momentum
