import polyak.Duality.Certificate

/-!
Article: Appendix A, reduction of infeasibility to finitely many lag constraints.
Use: weak compactness eliminates the infinite family before separation.
Proof: decreasing nonempty compact sets have nonempty intersection.
-/

noncomputable section

open MeasureTheory

namespace polyak.Duality

open Spectral

/-- Article: Pₘ. Use: exactly the minimizer constraint and the first M positive lags. -/
def FiniteFeasible (m : C(Frequency, ℂ)) (t : ℝ) (M : ℕ) (ν : Spectrum) (C : ℝ) : Prop :=
  |C| ≤ Waves.spectrumG ν m ∧ ∀ n : ℕ, 1 ≤ n → n ≤ M →
    0 ≤ Waves.spectrumA ν m t n - Waves.spectrumB ν m n + C * Real.sinh (n * t) ∧
    0 ≤ Waves.spectrumA ν m t n + Waves.spectrumB ν m n - C * Real.sinh (n * t)

/-- Article: all finite prefixes recover the complete spectral system. -/
theorem feasible_iff_all_finite (m : C(Frequency, ℂ)) (t : ℝ) (ν : Spectrum) (C : ℝ) :
    Waves.MixtureFeasible ν m C t ↔ ∀ M, FiniteFeasible m t M ν C := by
  constructor
  · intro h M
    exact ⟨h.1, fun n hn _ => h.2 n hn⟩
  · intro h
    exact ⟨(h 0).1, fun n hn => (h n).2 n hn le_rfl⟩

/-- Article: finite-memory feasibility is closed, including the two minimizer signs. -/
theorem isClosed_finiteFeasible (m : C(Frequency, ℂ)) (t : ℝ) (M : ℕ) :
    IsClosed {p : Spectrum × ℝ | FiniteFeasible m t M p.1 p.2} := by
  have hG := isClosed_le (continuous_snd.abs : Continuous (fun p : Spectrum × ℝ => |p.2|))
    (continuous_spectrumG (m := fun _ : Spectrum × ℝ => m) continuous_fst continuous_const)
  have hlag : IsClosed {p : Spectrum × ℝ | ∀ n : ℕ, 1 ≤ n → n ≤ M →
      0 ≤ Waves.spectrumA p.1 m t n - Waves.spectrumB p.1 m n + p.2 * Real.sinh (n * t) ∧
      0 ≤ Waves.spectrumA p.1 m t n + Waves.spectrumB p.1 m n - p.2 * Real.sinh (n * t)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro _hn
    apply isClosed_iInter
    intro _hM
    have ha := continuous_spectrumA (ν := fun p : Spectrum × ℝ => p.1)
      (m := fun _ => m) (t := fun _ => t) continuous_fst continuous_const continuous_const n
    have hb := continuous_spectrumB (ν := fun p : Spectrum × ℝ => p.1)
      (m := fun _ => m) continuous_fst continuous_const n
    have hc : Continuous (fun p : Spectrum × ℝ => p.2 * Real.sinh (n * t)) :=
      continuous_snd.mul continuous_const
    exact (isClosed_le continuous_const ((ha.sub hb).add hc)).inter
      (isClosed_le continuous_const ((ha.add hb).sub hc))
  exact hG.inter hlag

/-- Article: compactness of every finite prefix. Proof: the minimizer constraint bounds C. -/
theorem isCompact_finiteFeasible (m : C(Frequency, ℂ)) (t : ℝ) (M : ℕ) :
    IsCompact {p : Spectrum × ℝ | FiniteFeasible m t M p.1 p.2} := by
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))).of_isClosed_subset
    (isClosed_finiteFeasible m t M)
  intro p hp
  exact ⟨Set.mem_univ _, abs_le.mp (hp.1.trans (spectrumG_le_one p.1 m))⟩

/-- Article: the compactness finite-lag reduction, with no separation hypothesis. -/
theorem exists_infeasible_finite (m : C(Frequency, ℂ)) (t : ℝ)
    (h : ¬ ∃ (ν : Spectrum) (C : ℝ), Waves.MixtureFeasible ν m C t) :
    ∃ M : ℕ, ¬ ∃ (ν : Spectrum) (C : ℝ), FiniteFeasible m t M ν C := by
  by_contra hnone
  push Not at hnone
  let P : ℕ → Set (Spectrum × ℝ) := fun M => {p | FiniteFeasible m t M p.1 p.2}
  have hmono (M : ℕ) : P (M + 1) ⊆ P M := by
    intro p hp
    exact ⟨hp.1, fun n hn hM => hp.2 n hn (hM.trans (Nat.le_succ M))⟩
  have hnonempty (M : ℕ) : (P M).Nonempty := by
    obtain ⟨ν, C, hp⟩ := hnone M
    exact ⟨(ν, C), hp⟩
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed P
    hmono hnonempty (isCompact_finiteFeasible m t 0) (isClosed_finiteFeasible m t)
  apply h
  refine ⟨p.1, p.2, (feasible_iff_all_finite m t p.1 p.2).mpr ?_⟩
  exact Set.mem_iInter.mp hp

/-- Article: finite-memory compactness with an additional linear spectral equality.
Use: the future kernel restriction; no bound on the equality multiplier is assumed. -/
theorem isCompact_finiteFeasible_equality (m : C(Frequency, ℂ)) (t : ℝ) (M : ℕ)
    (e : C(Frequency, ℝ)) :
    IsCompact {p : Spectrum × ℝ | FiniteFeasible m t M p.1 p.2 ∧ (∫ c, e c ∂p.1) = 0} :=
  (isCompact_finiteFeasible m t M).inter_right
    (isClosed_eq ((ProbabilityMeasure.continuous_integral_continuousMap e).comp continuous_fst)
      continuous_const)

/-- Article: compact finite-lag reduction within an additional linear equality.
Use: infeasibility on a stationary kernel is already witnessed by finitely many lags.
Proof: retain the closed equality throughout the decreasing compact intersection. -/
theorem exists_infeasible_finite_equality (m : C(Frequency, ℂ)) (t : ℝ)
    (e : C(Frequency, ℝ))
    (h : ¬ ∃ (ν : Spectrum) (C : ℝ),
      Waves.MixtureFeasible ν m C t ∧ (∫ c, e c ∂ν) = 0) :
    ∃ M : ℕ, ¬ ∃ (ν : Spectrum) (C : ℝ),
      FiniteFeasible m t M ν C ∧ (∫ c, e c ∂ν) = 0 := by
  by_contra hnone
  push Not at hnone
  let P : ℕ → Set (Spectrum × ℝ) := fun M =>
    {p | FiniteFeasible m t M p.1 p.2 ∧ (∫ c, e c ∂p.1) = 0}
  have hmono (M : ℕ) : P (M + 1) ⊆ P M := by
    intro p hp
    exact ⟨⟨hp.1.1, fun n hn hM => hp.1.2 n hn (hM.trans (Nat.le_succ M))⟩, hp.2⟩
  have hnonempty (M : ℕ) : (P M).Nonempty := by
    obtain ⟨ν, C, hp⟩ := hnone M
    exact ⟨(ν, C), hp⟩
  have hclosed (M : ℕ) : IsClosed (P M) :=
    (isCompact_finiteFeasible_equality m t M e).isClosed
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed P
    hmono hnonempty (isCompact_finiteFeasible_equality m t 0 e) hclosed
  have hall := Set.mem_iInter.mp hp
  exact h ⟨p.1, p.2, (feasible_iff_all_finite m t p.1 p.2).mpr
    (fun M => (hall M).1), (hall 0).2⟩

end polyak.Duality
