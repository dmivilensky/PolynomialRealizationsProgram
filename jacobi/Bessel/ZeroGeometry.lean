import jacobi.Bessel.McMahonSquared

/-!
Article: jacobi, Proposition C.4.
The original complete positive-zero sequence has uniform linear growth
and a positive uniform gap. These estimates follow from its exact indexed
phase limit and strict genuine zero ordering; no gap hypothesis is added.
Use: obtains one uniform positive gap over the full original zero sequence before transferring its geometry to finite Jacobi spectra.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine consecutive Bessel-zero gaps tend to pi.
Use: obtains one uniform positive gap over the full original zero sequence before transferring its geometry to finite Jacobi spectra.
Article: jacobi, Lemma C.1.
Proof: subtract the proved indexed Weyl errors at k+1 and k; the literal phase grid increments by pi. -/
theorem positiveZero_gap_tendsto {a : ℝ} (ha : -1<a) :
    Tendsto (fun k : ℕ => positiveZero a ha (k+1)-positiveZero a ha k) atTop (𝓝 Real.pi) := by
  have h := (((positiveZero_phase_tendsto ha).comp (tendsto_add_atTop_nat 1)).sub
    (positiveZero_phase_tendsto ha)).add_const Real.pi
  simp only [sub_self,zero_add] at h
  convert h using 1
  ext k
  simp only [Function.comp_def,phaseGrid_add,Nat.cast_one,one_mul]
  ring

/-- A positive real sequence with a positive eventual lower bound has a uniform strictly positive lower bound.
Use: combines the genuine Bessel large-index gap limit with the finitely many original small-index positive gaps.
Article: jacobi, Proposition C.4.
Proof: a finite sum of positive reciprocals bounds every initial reciprocal;
its reciprocal is therefore a common positive lower bound. Take the minimum
with the genuine tail bound. -/
theorem positive_lower_all {f : ℕ → ℝ} (hf : ∀ k,0<f k) {d : ℝ} (hd : 0<d)
    (he : ∀ᶠ k : ℕ in atTop,d≤f k) : ∃ c : ℝ,0<c ∧ ∀ k,c≤f k := by
  -- The finite sum uses only the actual positive entries; no numerical lower-bound certificates for the initial segment are required.
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  let S := 1+∑ i∈Finset.range K,1/f i
  have hsum : 0≤∑ i∈Finset.range K,1/f i :=
    Finset.sum_nonneg (fun i _ => (div_pos (by norm_num) (hf i)).le)
  have hS : 0<S := by dsimp [S]; linarith
  refine ⟨min d (1/S),lt_min hd (by positivity),?_⟩
  intro k
  by_cases hk : K≤k
  · exact (min_le_left _ _).trans (hK k hk)
  · have hi : 1/f k≤∑ i∈Finset.range K,1/f i :=
      Finset.single_le_sum (s := Finset.range K) (f := fun i : ℕ => 1/f i)
        (fun i _ => (div_pos (by norm_num) (hf i)).le) (Finset.mem_range.mpr (by omega))
    have hb : 1/f k≤S := by dsimp [S]; linarith
    have hm := (div_le_iff₀ (hf k)).mp hb
    exact (min_le_right _ _).trans ((div_le_iff₀ hS).mpr (by nlinarith))

/-- All genuine consecutive Bessel zeros have one uniform strictly positive gap.
Use: transfers a uniform gap to every sufficiently large finite Jacobi zero list, including the growing first-half index range.
Article: jacobi, Proposition C.4.
Proof: the actual gap tends to pi, so it is eventually at least pi/2.
Every remaining original gap is positive by the already proved strict zero ordering. -/
theorem positiveZero_gap_lower {a : ℝ} (ha : -1<a) :
    ∃ c : ℝ,0<c ∧ ∀ k,c≤positiveZero a ha (k+1)-positiveZero a ha k := by
  have he := (positiveZero_gap_tendsto ha).eventually (Ioi_mem_nhds (show Real.pi/2<Real.pi by linarith [Real.pi_pos]))
  apply positive_lower_all (fun k => sub_pos.mpr (positiveZero_strictMono ha (Nat.lt_succ_self k)))
    (show 0<Real.pi/2 by positivity)
  exact he.mono (fun _ h => h.le)

/-- The genuine canonically numbered Bessel zeros grow linearly with uniform positive lower and upper constants.
Use: supplies the original spectral endpoint scale in Proposition B.1 (c), including every finite small index.
Article: jacobi, Proposition B.1.
Proof: the original uniform positive gap and positive first zero give the
linear lower bound by induction. The exact leading inverse-index bound
and explicit phase upper bound give the linear upper bound. -/
theorem positiveZero_linear_bounds {a : ℝ} (ha : -1<a) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ k : ℕ,c*(k+1:ℝ)≤positiveZero a ha k ∧ positiveZero a ha k≤C*(k+1:ℝ) := by
  -- Both constants come from already proved original zero geometry, with the true first zero retained in the lower constant.
  obtain ⟨d,hd,hgap⟩ := positiveZero_gap_lower ha
  obtain ⟨A,hA,hfirst⟩ := positiveZero_phase_bound ha
  let c := min d (positiveZero a ha 0)
  let L := Real.pi*(|a|+2)
  have hc : 0<c := lt_min hd (positiveZero_properties ha 0).1
  refine ⟨c,L+A,hc,by dsimp [L]; positivity,?_⟩
  have hlo : ∀ k : ℕ,c*(k+1:ℝ)≤positiveZero a ha k := by
    intro k
    induction k with
    | zero => simpa only [Nat.cast_zero,zero_add,mul_one] using min_le_right d (positiveZero a ha 0)
    | succ k ih =>
      have hg := hgap k
      have hcD : c≤d := min_le_left _ _
      push_cast
      linarith
  intro k
  refine ⟨hlo k,?_⟩
  have ht : 1≤(k+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hh := (abs_le.mp (hfirst k)).2
  have hp := phaseGrid_upper a k
  have hdiv : A/(k+1:ℝ)≤A := div_le_self hA.le ht
  have hmul : A≤A*(k+1:ℝ) := by nlinarith
  dsimp [L]
  nlinarith

end
end jacobi.Bessel
