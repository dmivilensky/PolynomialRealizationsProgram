import polyak.Growth.HorizonSegment
import polyak.Growth.Rate

/-!
Article: Appendix C, the exact growth envelope of finite-memory H-segments.
Use: this is a supremum over actual admissible finite tables in every finite dimension.
Its finiteness, positivity, submultiplicativity and genuine root limit are proved.
-/

namespace polyak.Growth.FiniteHorizon
noncomputable section
open Set Filter
open scoped Topology

def segmentRatios (A B β : ℝ) (H n : ℕ) : Set ℝ :=
  {r | ∃ d : ℕ,∃ s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,
    stateNorm s.x 0≠0 ∧ r=stateNorm s.x n/stateNorm s.x 0}

/-- Article: the exact finite-memory envelope Γ_H(n). -/
def envelope (A B β : ℝ) (H n : ℕ) : ℝ := sSup (insert 0 (segmentRatios A B β H n))

theorem ratios_bddAbove (A B β : ℝ) (H n : ℕ) :
    BddAbove (insert 0 (segmentRatios A B β H n)) := by
  refine ⟨(1+|A|+|B|+|β|)^n,?_⟩
  rintro r (rfl | ⟨d,s,hs,rfl⟩)
  · positivity
  · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).mpr
    exact s.stateNorm_le n le_rfl

theorem envelope_nonneg (A B β : ℝ) (H n : ℕ) : 0 ≤ envelope A B β H n :=
  le_csSup (ratios_bddAbove A B β H n) (mem_insert _ _)

theorem envelope_le (A B β : ℝ) (H n : ℕ) :
    envelope A B β H n ≤ (1+|A|+|B|+|β|)^n := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨d,s,hs,rfl⟩)
  · positivity
  · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).mpr
    exact s.stateNorm_le n le_rfl

theorem stateNorm_le_envelope {A B β : ℝ} {H n d : ℕ}
    (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n) :
    stateNorm s.x n ≤ envelope A B β H n*stateNorm s.x 0 := by
  by_cases hs : stateNorm s.x 0=0
  · rw [s.stateNorm_eq_zero_of_zero hs n le_rfl,hs,mul_zero]
  · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).mp
    exact le_csSup (ratios_bddAbove A B β H n) (mem_insert_of_mem _ ⟨d,s,hs,rfl⟩)

/-- Article: finite-span compression makes the same Γ_H valid in every real Hilbert space. -/
theorem stateNorm_le_envelope_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {A B β : ℝ} {H n : ℕ} (s : HSegment E A B β H n) :
    stateNorm s.x n ≤ envelope A B β H n*stateNorm s.x 0 := by
  obtain ⟨d,q,hq⟩ := s.exists_euclidean
  simpa only [hq n le_rfl,hq 0 (Nat.zero_le _)] using stateNorm_le_envelope q

theorem stateNorm_window_le_envelope {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {A B β : ℝ} {H n : ℕ} (s : HSegment E A B β H n)
    (l p : ℕ) (h : l+p ≤ n) :
    stateNorm s.x (l+p) ≤ envelope A B β H p*stateNorm s.x l := by
  simpa only [HSegment.stateNorm_restrict,Nat.add_zero] using
    stateNorm_le_envelope_hilbert (s.restrict l p h)

/-- Article: every ordinary segment is admissible for every finite memory. -/
theorem full_envelope_le (A B β : ℝ) (H n : ℕ) :
    Growth.envelope A B β n ≤ envelope A B β H n := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨d,s,hs,rfl⟩)
  · exact envelope_nonneg A B β H n
  · exact le_csSup (ratios_bddAbove A B β H n)
      (mem_insert_of_mem _ ⟨d,HSegment.ofSegment s H,hs,rfl⟩)

/-- Article: on a horizon shorter than the retained memory, Γ_H is exactly Γ. -/
theorem envelope_eq_full_of_length_le (A B β : ℝ) {H n : ℕ} (hn : n ≤ H+1) :
    envelope A B β H n=Growth.envelope A B β n := by
  apply le_antisymm _ (full_envelope_le A B β H n)
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨d,s,hs,rfl⟩)
  · exact Growth.envelope_nonneg A B β n
  · obtain ⟨q,hq,_⟩ := (s.raw hn).exists_completion
    change q.x=s.x at hq
    exact le_csSup (Growth.segmentRatios_bddAbove A B β n)
      (mem_insert_of_mem _ ⟨d,q,by simpa only [hq] using hs,by simp only [hq]⟩)

/-- Article: retaining more interpolation pairs can only decrease Γ_H. -/
theorem envelope_antitone_memory (A B β : ℝ) {H K : ℕ} (hHK : H ≤ K) (n : ℕ) :
    envelope A B β K n ≤ envelope A B β H n := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨d,s,hs,rfl⟩)
  · exact envelope_nonneg A B β H n
  · exact le_csSup (ratios_bddAbove A B β H n)
      (mem_insert_of_mem _ ⟨d,s.weaken H hHK,hs,rfl⟩)

/-- Article: Γ_H is genuinely submultiplicative, including zero intermediate states. -/
theorem envelope_submultiplicative (A B β : ℝ) (H p q : ℕ) :
    envelope A B β H (p+q) ≤ envelope A B β H p*envelope A B β H q := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨d,s,hs,rfl⟩)
  · exact mul_nonneg (envelope_nonneg A B β H p) (envelope_nonneg A B β H q)
  · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).mpr
    have hq := stateNorm_le_envelope (s.restrict p q le_rfl)
    have hp := stateNorm_le_envelope (s.restrict 0 p (by omega))
    rw [HSegment.stateNorm_restrict,HSegment.stateNorm_restrict] at hq hp
    simp only [Nat.add_zero,Nat.zero_add] at hq hp
    calc
      stateNorm s.x (p+q) ≤ envelope A B β H q*stateNorm s.x p := hq
      _ ≤ envelope A B β H q*(envelope A B β H p*stateNorm s.x 0) :=
        mul_le_mul_of_nonneg_left hp (envelope_nonneg A B β H q)
      _ = _ := by ring

theorem envelope_zero (A B β : ℝ) (H : ℕ) : envelope A B β H 0=1 := by
  apply le_antisymm (by simpa using envelope_le A B β H 0)
  simpa only [Growth.envelope_zero] using full_envelope_le A B β H 0

theorem envelope_pos {A B β : ℝ} (hB : B≠0) (H n : ℕ) : 0<envelope A B β H n :=
  (Growth.envelope_pos hB n).trans_le (full_envelope_le A B β H n)

def growthExponent (A B β : ℝ) (H : ℕ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (envelope A B β H n)/n) '' Ici 1)

/-- Article: the exact finite-memory growth rate. -/
def growthRate (A B β : ℝ) (H : ℕ) : ℝ := Real.exp (growthExponent A B β H)

theorem growthRate_pos (A B β : ℝ) (H : ℕ) : 0<growthRate A B β H := Real.exp_pos _

theorem log_subadditive {A B β : ℝ} (hB : B≠0) (H : ℕ) :
    Subadditive (fun n => Real.log (envelope A B β H n)) := by
  intro p q
  calc
    _ ≤ Real.log (envelope A B β H p*envelope A B β H q) :=
      Real.log_le_log (envelope_pos hB H _) (envelope_submultiplicative A B β H p q)
    _ = _ := Real.log_mul (envelope_pos hB H _).ne' (envelope_pos hB H _).ne'

theorem log_bddBelow {A B β : ℝ} (hB : B≠0) (H : ℕ) :
    BddBelow (range (fun n : ℕ => Real.log (envelope A B β H n)/n)) := by
  obtain ⟨b,hb,hl⟩ := Growth.envelope_lower_base (A:=A) (β:=β) hB
  refine ⟨min (Real.log b) 0,?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n=0
  · simp [hn]
  · have hn' : (0 : ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh := Real.log_le_log (pow_pos hb n) ((hl n).trans (full_envelope_le A B β H n))
    rw [Real.log_pow] at hh
    exact (min_le_left _ _).trans ((le_div_iff₀ hn').mpr (by nlinarith))

/-- Article: Fekete gives a genuine logarithmic limit for the finite-memory class. -/
theorem tendsto_envelope_log_div {A B β : ℝ} (hB : B≠0) (H : ℕ) :
    Tendsto (fun n : ℕ => Real.log (envelope A B β H n)/n) atTop
      (𝓝 (growthExponent A B β H)) := by
  simpa only [Subadditive.lim,growthExponent] using
    (log_subadditive hB H).tendsto_lim (log_bddBelow hB H)

/-- Article: the root limit defining ρ_H exists and is positive. -/
theorem tendsto_envelope_root {A B β : ℝ} (hB : B≠0) (H : ℕ) :
    Tendsto (fun n : ℕ => envelope A B β H n^((n : ℝ)⁻¹)) atTop
      (𝓝 (growthRate A B β H)) := by
  have hh := (Real.continuous_exp.tendsto _).comp (tendsto_envelope_log_div (A:=A) (β:=β) hB H)
  simpa only [Function.comp_def,growthRate,Real.rpow_def_of_pos (envelope_pos hB H _),
    div_eq_mul_inv] using hh

/-- Article: the finite-memory relaxation has rate at least the exact free rate. -/
theorem full_growthRate_le {A B β : ℝ} (hB : B≠0) (H : ℕ) :
    Growth.growthRate A B β ≤ growthRate A B β H := by
  apply le_of_tendsto_of_tendsto (Growth.tendsto_envelope_root hB) (tendsto_envelope_root hB H)
  exact Eventually.of_forall (fun n => Real.rpow_le_rpow (Growth.envelope_nonneg A B β n)
    (full_envelope_le A B β H n) (by positivity))

/-- Article: Γ_H(n)≥ρ_Hⁿ is valid on every horizon, including zero. -/
theorem growthRate_pow_le_envelope {A B β : ℝ} (hB : B≠0) (H n : ℕ) :
    growthRate A B β H^n ≤ envelope A B β H n := by
  by_cases hn : n=0
  · simp [hn,envelope_zero]
  · have hh := (log_subadditive (A:=A) (β:=β) hB H).lim_le_div (log_bddBelow hB H) hn
    have hn' : (0 : ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh' : growthExponent A B β H ≤ Real.log (envelope A B β H n)/n := by
      simpa only [Subadditive.lim,growthExponent] using hh
    have hi := (le_div_iff₀ hn').mp hh'
    rw [growthRate,← Real.exp_nat_mul,← Real.exp_log (envelope_pos hB H n)]
    apply Real.exp_le_exp.mpr
    nlinarith

theorem growthRate_le_root {A B β : ℝ} (hB : B≠0) (H : ℕ) {n : ℕ} (hn : n≠0) :
    growthRate A B β H ≤ envelope A B β H n^((n : ℝ)⁻¹) := by
  have hh := Real.rpow_le_rpow (pow_pos (growthRate_pos A B β H) n).le
    (growthRate_pow_le_envelope hB H n) (by positivity : 0 ≤ (n : ℝ)⁻¹)
  simpa only [Real.pow_rpow_inv_natCast (growthRate_pos A B β H).le hn] using hh

/-- Article: every strict exponential majorant of Γ eventually majorizes the finite-memory rates. -/
theorem eventually_growthRate_lt {A B β R : ℝ} (hB : B≠0) (hR : Growth.growthRate A B β<R) :
    ∀ᶠ H : ℕ in atTop,growthRate A B β H<R := by
  obtain ⟨n,hn,hnR⟩ := ((Growth.tendsto_envelope_root (A:=A) (β:=β) hB).eventually
    (gt_mem_nhds hR) |>.and (eventually_gt_atTop 0)).exists
  filter_upwards [eventually_ge_atTop n] with H hH
  have hfull := envelope_eq_full_of_length_le A B β (H:=H) (n:=n) (by omega)
  exact (growthRate_le_root hB H (by omega : n≠0)).trans_lt (by rwa [hfull])

/-- Article: increasing the interpolation memory recovers the exact original free rate. -/
theorem tendsto_growthRate_memory {A B β : ℝ} (hB : B≠0) :
    Tendsto (growthRate A B β) atTop (𝓝 (Growth.growthRate A B β)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun H => hb.trans_le (full_growthRate_le hB H))
  · intro b hb
    exact eventually_growthRate_lt hB hb

/-- Article: finite Γ_H has uniform majorants at every strictly larger exponential factor. -/
theorem exists_envelope_le_mul_pow {A B β R : ℝ} {H : ℕ} (hB : B≠0)
    (hR : growthRate A B β H<R) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope A B β H n ≤ C*R^n := by
  have hRp : 0<R := (growthRate_pos A B β H).trans hR
  have he : growthExponent A B β H<Real.log R := by
    rw [← Real.exp_lt_exp,Real.exp_log hRp]
    exact hR
  have hevent : ∀ᶠ n : ℕ in atTop,envelope A B β H n ≤ R^n := by
    filter_upwards [(tendsto_envelope_log_div (A:=A) (β:=β) hB H).eventually (gt_mem_nhds he),
      eventually_gt_atTop 0] with n hn hn0
    have hh := (div_lt_iff₀ (Nat.cast_pos.mpr hn0 : (0 : ℝ)<n)).mp hn
    rw [← Real.exp_log (envelope_pos hB H n),← Real.rpow_natCast,Real.rpow_def_of_pos hRp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  let C : ℝ := 1+∑ k∈Finset.range N,envelope A B β H k/R^k
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ =>
    div_nonneg (envelope_nonneg A B β H k) (pow_pos hRp k).le))
  refine ⟨C,zero_lt_one.trans_le hC,fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (by nlinarith [pow_pos hRp n])
  · have hs : envelope A B β H n/R^n ≤ ∑ k∈Finset.range N,envelope A B β H k/R^k :=
      Finset.single_le_sum (fun k _ => div_nonneg (envelope_nonneg A B β H k) (pow_pos hRp k).le)
        (Finset.mem_range.mpr (by omega))
    apply (div_le_iff₀ (pow_pos hRp n)).mp
    dsimp only [C]
    linarith

end
end polyak.Growth.FiniteHorizon
