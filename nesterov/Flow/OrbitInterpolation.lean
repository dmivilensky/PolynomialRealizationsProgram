import nesterov.Flow.SpiralOperator
import nesterov.Flow.ConvexExtension

/-!
Article: Appendix B, Lemma `creduce`.
Use: the exact equivalence between the continuous-lag program and every
convex support inequality on the whole orbit together with its minimizer.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

abbrev OrbitIndex := Option {t : ℝ // 0 ≤ t}

variable {J : Type*} [Fintype J]

def Spectrum.jetPoint (ν : Spectrum J) (c : ℝ) : OrbitIndex → EuclideanSpace ℂ J
  | none => 0
  | some t => ν.orbit c t

def Spectrum.jetGradient (ν : Spectrum J) (θ m c : ℝ) : OrbitIndex → EuclideanSpace ℂ J
  | none => 0
  | some t => ν.forcedGradient θ m c t

def Spectrum.jetValue (ν : Spectrum J) (θ m c : ℝ) : OrbitIndex → ℝ
  | none => 0
  | some t => ν.orbitValue θ m c t

theorem Spectrum.supportFeasible_of_program (ν : Spectrum J) {θ m c : ℝ}
    (hc : 0 < c) (hct : c ≤ θ / 2) (h : ν.Feasible θ m c) :
    SupportFeasible (ν.jetPoint c) (ν.jetGradient θ m c) (ν.jetValue θ m c) := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none => simp [jetPoint, jetGradient, jetValue]
    | some t =>
      change ν.orbitValue θ m c t + ⟪ν.forcedGradient θ m c t, 0 - ν.orbit c t⟫_ℝ ≤ 0
      simp only [zero_sub, inner_neg_right]
      linarith [ν.minimizer_gap_nonneg hc h t]
  | some s =>
    cases j with
    | none =>
      change 0 + ⟪(0 : EuclideanSpace ℂ J), ν.orbit c s - 0⟫_ℝ ≤ ν.orbitValue θ m c s
      simpa using ν.orbitValue_nonneg hc hct h s
    | some t =>
      change ν.orbitValue θ m c t +
        ⟪ν.forcedGradient θ m c t, ν.orbit c s - ν.orbit c t⟫_ℝ ≤ ν.orbitValue θ m c s
      rcases lt_trichotomy (t : ℝ) (s : ℝ) with hlt | heq | hgt
      · have hlag := ν.forward_slack hc θ m t ((s : ℝ) - t)
        rw [show (t : ℝ) + ((s : ℝ) - t) = s by ring] at hlag
        have hnonneg := mul_nonneg (Real.exp_pos (-2 * c * (t : ℝ) - c * ((s : ℝ) - t))).le
          (h.1 _ (sub_pos.mpr hlt))
        linarith
      · have ht : t = s := Subtype.ext heq
        subst t
        simp
      · have hlag := ν.backward_slack hc θ m s ((t : ℝ) - s)
        rw [show (s : ℝ) + ((t : ℝ) - s) = t by ring] at hlag
        have hnonneg := mul_nonneg (Real.exp_pos (-2 * c * (s : ℝ) - c * ((t : ℝ) - s))).le
          (h.2.1 _ (sub_pos.mpr hgt))
        linarith

theorem Spectrum.program_of_supportFeasible (ν : Spectrum J) {θ m c : ℝ}
    (hc : 0 < c)
    (h : SupportFeasible (ν.jetPoint c) (ν.jetGradient θ m c) (ν.jetValue θ m c)) :
    ν.Feasible θ m c := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have hh := h (some ⟨q, hq.le⟩) (some ⟨0, le_rfl⟩)
    change ν.orbitValue θ m c 0 + ⟪ν.forcedGradient θ m c 0,
      ν.orbit c q - ν.orbit c 0⟫_ℝ ≤ ν.orbitValue θ m c q at hh
    have hs := ν.forward_slack hc θ m 0 q
    simp only [zero_add] at hs
    have hp : 0 < Real.exp (-2 * c * 0 - c * q) := Real.exp_pos _
    exact nonneg_of_mul_nonneg_left (by linarith) hp
  · intro q hq
    have hh := h (some ⟨0, le_rfl⟩) (some ⟨q, hq.le⟩)
    change ν.orbitValue θ m c q + ⟪ν.forcedGradient θ m c q,
      ν.orbit c 0 - ν.orbit c q⟫_ℝ ≤ ν.orbitValue θ m c 0 at hh
    have hs := ν.backward_slack hc θ m 0 q
    simp only [zero_add] at hs
    have hp : 0 < Real.exp (-2 * c * 0 - c * q) := Real.exp_pos _
    exact nonneg_of_mul_nonneg_left (by linarith) hp
  · have hh := h none (some ⟨0, le_rfl⟩)
    change ν.orbitValue θ m c 0 +
      ⟪ν.forcedGradient θ m c 0, 0 - ν.orbit c 0⟫_ℝ ≤ 0 at hh
    simp only [zero_sub, inner_neg_right] at hh
    have hs := ν.minimizer_gap hc θ m 0
    rw [ν.minimizer_gap_moment hc] at hs
    simp only [mul_zero, Real.exp_zero, one_mul] at hs
    have hdiv : 0 ≤ ((3 * c - θ) * (∑ j, ν.weight j * ν.frequency j ^ 2) -
        c * delta θ m c) / (2 * c) := by linarith
    have hnum := (le_div_iff₀ (show 0 < 2 * c by positivity)).mp hdiv
    linarith

/-- Lemma `creduce`: no lag, time, or minimizer support inequality is lost. -/
theorem Spectrum.program_iff_supportFeasible (ν : Spectrum J) {θ m c : ℝ}
    (hc : 0 < c) (hct : c ≤ θ / 2) :
    ν.Feasible θ m c ↔
      SupportFeasible (ν.jetPoint c) (ν.jetGradient θ m c) (ν.jetValue θ m c) :=
  ⟨ν.supportFeasible_of_program hc hct, ν.program_of_supportFeasible hc⟩

theorem Spectrum.jets_bounded (ν : Spectrum J) {c : ℝ} (hc : 0 < c) (θ m : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : OrbitIndex,
      |ν.jetValue θ m c i| ≤ B ∧ ‖ν.jetGradient θ m c i‖ ≤ B ∧ ‖ν.jetPoint c i‖ ≤ B := by
  let V := ∑ j, ν.weight j * atomValue θ m c (ν.frequency j)
  let K := ‖ν.gradientOperator θ m c‖
  let B := 1 + |V| + K
  have hK : 0 ≤ K := norm_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro i
  cases i with
  | none => simpa [jetValue, jetPoint, jetGradient] using And.intro hB (And.intro hB hB)
  | some t =>
    have he1 : Real.exp (-c * (t : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [t.property])
    have he2 : Real.exp (-2 * c * (t : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [t.property])
    change |Real.exp (-2 * c * (t : ℝ)) * V| ≤ B ∧
      ‖ν.forcedGradient θ m c t‖ ≤ B ∧ ‖ν.orbit c t‖ ≤ B
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have hh := mul_le_mul_of_nonneg_right he2 (abs_nonneg V)
      dsimp [B]
      linarith
    · have hh := ν.forcedGradient_norm_le θ m c t
      have hk := mul_le_mul_of_nonneg_left he1 hK
      dsimp [B, K] at *
      linarith [abs_nonneg V]
    · rw [ν.orbit_norm]
      dsimp [B]
      linarith [abs_nonneg V]

/-- Lemma `creduce`, in its full convex interpolation form.  The origin is
included as an actual datum with value and subgradient zero; the potential
is globally finite and convex on the whole real Hilbert space. -/
theorem Spectrum.program_iff_convex_interpolant (ν : Spectrum J) {θ m c : ℝ}
    (hc : 0 < c) (hct : c ≤ θ / 2) :
    ν.Feasible θ m c ↔
      ∃ f : EuclideanSpace ℂ J → ℝ, ConvexOn ℝ Set.univ f ∧ f 0 = 0 ∧
        (∀ u, 0 ≤ f u) ∧ ∀ t : ℝ, 0 ≤ t →
          f (ν.orbit c t) = ν.orbitValue θ m c t ∧
          ∀ u, f (ν.orbit c t) + ⟪ν.forcedGradient θ m c t, u - ν.orbit c t⟫_ℝ ≤ f u := by
  constructor
  · intro h
    obtain ⟨B, hB, hbounded⟩ := ν.jets_bounded hc θ m
    obtain ⟨f, hconv, hf0, hfnonneg, hdata⟩ := exists_convex_support_interpolant
      (ν.supportFeasible_of_program hc hct h) hB hbounded none rfl rfl rfl
    exact ⟨f, hconv, hf0, hfnonneg, fun t ht => hdata (some ⟨t, ht⟩)⟩
  · rintro ⟨f, _, hf0, hfnonneg, hdata⟩
    apply ν.program_of_supportFeasible hc
    intro i j
    cases j with
    | none =>
      cases i with
      | none => simp [jetPoint, jetValue, jetGradient]
      | some s =>
        change 0 + ⟪(0 : EuclideanSpace ℂ J), ν.orbit c s - 0⟫_ℝ ≤ ν.orbitValue θ m c s
        rw [← (hdata s s.property).1]
        simpa using hfnonneg (ν.orbit c s)
    | some t =>
      have hh := (hdata t t.property).2 (ν.jetPoint c i)
      rw [(hdata t t.property).1] at hh
      change ν.orbitValue θ m c t +
        ⟪ν.forcedGradient θ m c t, ν.jetPoint c i - ν.orbit c t⟫_ℝ ≤ ν.jetValue θ m c i
      cases i with
      | none => simpa only [jetPoint, jetValue, hf0] using hh
      | some s => simpa only [jetPoint, jetValue, (hdata s s.property).1] using hh

end nesterov.Flow
