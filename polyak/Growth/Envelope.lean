import polyak.Growth.Segment
import polyak.Interpolation.Extension
import polyak.Waves.Dynamics
import polyak.Waves.Interpolation
import polyak.Dynamics.QuadraticRate

/-!
Article: Appendix A, Lemma growth envelope.
Use: the exact dimension-uniform supremum over finite admissible segments.
Proof: restriction of a table and absorption of a zero intermediate state.
-/

namespace polyak.Growth
noncomputable section
open Set

/-- Article: Γ(p). Use: genuine free-state ratios over all finite dimensions. -/
def segmentRatios (A B β : ℝ) (p : ℕ) : Set ℝ :=
  {r | ∃ d : ℕ, ∃ s : Segment (EuclideanSpace ℝ (Fin d)) A B β p,
    stateNorm s.x 0 ≠ 0 ∧ r = stateNorm s.x p / stateNorm s.x 0}

/-- Article: Γ(p). Use: a real supremum with an explicit harmless zero lower bound. -/
def envelope (A B β : ℝ) (p : ℕ) : ℝ := sSup (insert 0 (segmentRatios A B β p))

/-- Article: finite Γ. Use: every ratio is bounded independently of dimension. -/
theorem segmentRatio_le {A B β r : ℝ} {p : ℕ} (hr : r ∈ segmentRatios A B β p) :
    r ≤ (1+|A|+|B|+|β|)^p := by
  obtain ⟨d,s,hs,rfl⟩ := hr
  exact (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).2
    (s.stateNorm_le p le_rfl)

/-- Article: finite Γ. Use: justify every conditional supremum inequality. -/
theorem segmentRatios_bddAbove (A B β : ℝ) (p : ℕ) :
    BddAbove (insert 0 (segmentRatios A B β p)) := by
  refine ⟨(1+|A|+|B|+|β|)^p, ?_⟩
  intro r hr
  rcases hr with rfl | hr
  · positivity
  · exact segmentRatio_le hr

/-- Article: Γ≥0. Use: taking powers, logarithms and suprema only after bounds. -/
theorem envelope_nonneg (A B β : ℝ) (p : ℕ) : 0 ≤ envelope A B β p :=
  le_csSup (segmentRatios_bddAbove A B β p) (mem_insert _ _)

/-- Article: finite Γ. Use: a completely explicit finite-horizon majorant. -/
theorem envelope_le (A B β : ℝ) (p : ℕ) :
    envelope A B β p ≤ (1+|A|+|B|+|β|)^p := by
  apply csSup_le (insert_nonempty _ _)
  intro r hr
  rcases hr with rfl | hr
  · positivity
  · exact segmentRatio_le hr

/-- Article: Γ dominates every segment. Use: the actual ratio belongs to its defining set. -/
theorem stateNorm_le_envelope {A B β : ℝ} {n : ℕ} {d : ℕ}
    (s : Segment (EuclideanSpace ℝ (Fin d)) A B β n) :
    stateNorm s.x n ≤ envelope A B β n * stateNorm s.x 0 := by
  by_cases hs : stateNorm s.x 0 = 0
  · rw [s.stateNorm_eq_zero_of_zero hs n le_rfl, hs, mul_zero]
  · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).1
    exact le_csSup (segmentRatios_bddAbove A B β n) (mem_insert_of_mem _ ⟨d,s,hs,rfl⟩)

/-- Article: Γ window bound. Use: any consecutive state pair can serve as free initial state. -/
theorem stateNorm_window_le_envelope {A B β : ℝ} {n : ℕ} {d : ℕ}
    (s : Segment (EuclideanSpace ℝ (Fin d)) A B β n) (l p : ℕ) (h : l+p ≤ n) :
    stateNorm s.x (l+p) ≤ envelope A B β p * stateNorm s.x l := by
  simpa only [Segment.stateNorm_restrict, Nat.add_zero] using
    stateNorm_le_envelope (s.restrict l p h)

/-- Article: submultiplicativity. Use: zero intermediate states are treated without division. -/
theorem envelope_submultiplicative (A B β : ℝ) (p q : ℕ) :
    envelope A B β (p+q) ≤ envelope A B β p * envelope A B β q := by
  apply csSup_le (insert_nonempty _ _)
  intro r hr
  rcases hr with rfl | ⟨d,s,hs,rfl⟩
  · exact mul_nonneg (envelope_nonneg A B β p) (envelope_nonneg A B β q)
  · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).2
    calc
      stateNorm s.x (p+q) ≤ envelope A B β q * stateNorm s.x p :=
        stateNorm_window_le_envelope s p q le_rfl
      _ ≤ envelope A B β q * (envelope A B β p * stateNorm s.x 0) := by
        apply mul_le_mul_of_nonneg_left _ (envelope_nonneg A B β q)
        simpa using stateNorm_window_le_envelope s 0 p (by omega)
      _ = _ := by ring

/-- Article: Γ dominates Hilbert-space segments. Use: finite-span compression preserves the ratio. -/
theorem stateNorm_le_envelope_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {A B β : ℝ} {n : ℕ} (s : Segment E A B β n) :
    stateNorm s.x n ≤ envelope A B β n * stateNorm s.x 0 := by
  obtain ⟨d,q,hq⟩ := s.exists_euclidean
  simpa only [hq n le_rfl, hq 0 (Nat.zero_le _)] using stateNorm_le_envelope q

/-- Article: actual normalized segments. Use: construct all interpolation data from one function. -/
def Segment.ofNormalized {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {A B β : ℝ} {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (x : ℕ → E) (n : ℕ)
    (hrec : ∀ k, k < n → x (k+2) = A • x (k+1) +
      B • gradient ψ (x (k+1)) - β • x k) : Segment E A B β n where
  x := x
  σ k := gradient ψ (x k)
  value k := ψ (x k)
  interpolation i _ j _ := hψ.tableFeasible x i j
  origin i _ := by
    have hh := hψ.tableFeasible (fun b : Bool => if b then x i else 0) false true
    simpa only [Bool.false_eq_true, ↓reduceIte, hψ.value_zero, hψ.gradient_zero,
      zero_add, sub_zero, Interpolation.datumT, Interpolation.datumR] using hh
  recurrence := hrec

/-- Article: Γ(0)=1. Use: include the exact zero horizon. -/
theorem envelope_zero (A B β : ℝ) : envelope A B β 0 = 1 := by
  apply le_antisymm
  · simpa using envelope_le A B β 0
  · let s : Segment ℝ A B β 0 :=
      { x := fun _ => 1
        σ := fun _ => 0
        value := fun _ => 0
        interpolation := by intros; simp [Interpolation.datumT, Interpolation.datumR]
        origin := by intros; norm_num
        recurrence := by intros; omega }
    have h : 0 < stateNorm s.x 0 := by
      exact (norm_left_le_stateNorm s.x 0).trans_lt' (by norm_num [s])
    have hh := stateNorm_le_envelope_hilbert s
    nlinarith

/-- Article: spectral lower bound for Γ. Use: all feasible probability spectra contribute. -/
def Segment.ofMixture {A B β C t : ℝ} (ν : Spectral.Spectrum) (hB : B ≠ 0)
    (h : Waves.MixtureFeasible ν (Waves.multiplierMap A B β t) C t) (n : ℕ) :
    Segment (Waves.WaveSpace ν) A B β n where
  x k := Waves.mixturePosition ν t (some k)
  σ k := Waves.mixtureGradient ν (Waves.multiplierMap A B β t) t (some k)
  value k := Waves.mixtureValue ν (Waves.multiplierMap A B β t) C t (some k)
  interpolation i _ j _ := (Waves.mixture_tableFeasible_iff _ _ _ _).mpr h (some i) (some j)
  origin i _ := by
    have hh := (Waves.mixture_tableFeasible_iff _ _ _ _).mpr h none (some i)
    simpa only [Interpolation.datumT, Interpolation.datumR, Waves.mixturePosition_none,
      Waves.mixtureGradient_none, Waves.mixtureValue_none, zero_add, sub_zero] using hh
  recurrence k _ := Waves.mixture_recurrence ν A B β t hB k

/-- Article: state norm of a wave. Use: the common factor cancels exactly in state ratios. -/
theorem mixture_stateNorm (ν : Spectral.Spectrum) (t : ℝ) (k : ℕ) :
    stateNorm (fun k => Waves.mixturePosition ν t (some k)) k =
      Real.exp (k*t) * Real.sqrt (1+Real.exp t^2) := by
  apply (sq_eq_sq₀ (stateNorm_nonneg _ _) (by positivity)).mp
  rw [stateNorm_sq, Waves.norm_mixturePosition, Waves.norm_mixturePosition]
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have he : Real.exp ((k+1 : ℕ)*t) = Real.exp (k*t)*Real.exp t := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add]
  rw [he]
  ring

/-- Article: feasible spectrum lower bound. Use: no periodicity or finite-support assumption. -/
theorem exp_le_envelope {A B β C t : ℝ} (ν : Spectral.Spectrum) (hB : B ≠ 0)
    (h : Waves.MixtureFeasible ν (Waves.multiplierMap A B β t) C t) (n : ℕ) :
    Real.exp (n*t) ≤ envelope A B β n := by
  have hh := stateNorm_le_envelope_hilbert (Segment.ofMixture ν hB h n)
  change stateNorm (fun k => Waves.mixturePosition ν t (some k)) n ≤
    envelope A B β n * stateNorm (fun k => Waves.mixturePosition ν t (some k)) 0 at hh
  rw [mixture_stateNorm, mixture_stateNorm] at hh
  simp only [Nat.cast_zero, zero_mul, Real.exp_zero, one_mul] at hh
  exact (mul_le_mul_iff_left₀ (Real.sqrt_pos.2 (by positivity))).mp hh

end
end polyak.Growth
