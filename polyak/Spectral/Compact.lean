import polyak.Spectral.Feasibility
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
Article: Appendix A, compactness lemma and existence of V.
Use: closedness for every fixed lag and compactness of the full infinite system.
Proof: continuous moments, closed intersections, and compact probability measures.
Source: mathlib's compact-space Prokhorov theorem.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace polyak.Spectral

/-- Article: weak topology. Proof: integration of a continuous map is continuous. -/
theorem continuous_avg {f : Frequency → ℝ} (hf : Continuous f) :
    Continuous (fun ν : Spectrum => avg ν f) :=
  ProbabilityMeasure.continuous_integral_continuousMap (⟨f, hf⟩ : C(Frequency, ℝ))

/-- Article: joint continuity of g averages. Use: closure with moving twist and measure. -/
theorem continuous_meanG {X : Type*} [TopologicalSpace X] {ν : X → Spectrum}
    {u : X → ℝ} (hν : Continuous ν) (hu : Continuous u) :
    Continuous (fun x => meanG (ν x) (u x)) := by
  unfold meanG
  exact (continuous_const.sub ((continuous_avg (by fun_prop)).comp hν)).sub (hu.pow 2)

/-- Article: joint continuity of a averages. Use: closure with moving parameters. -/
theorem continuous_meanA {X : Type*} [TopologicalSpace X] {ν : X → Spectrum}
    {u t : X → ℝ} (hν : Continuous ν) (hu : Continuous u) (ht : Continuous t) (n : ℕ) :
    Continuous (fun x => meanA (ν x) (u x) (t x) n) := by
  have hT : Continuous (fun c : Frequency => chebT n c) :=
    (continuous_chebT n).comp continuous_subtype_val
  have hw : Continuous (fun c : Frequency => (1 - (c : ℝ) ^ 2) * chebT n c) :=
    (continuous_const.sub (continuous_subtype_val.pow 2)).mul hT
  unfold meanA
  exact (((Real.continuous_cosh.comp (continuous_const.mul ht)).mul (continuous_meanG hν hu)).sub
    ((continuous_avg hw).comp hν)).add ((hu.pow 2).mul ((continuous_avg hT).comp hν))

/-- Article: joint continuity of b averages. Use: closure with moving twist and measure. -/
theorem continuous_meanB {X : Type*} [TopologicalSpace X] {ν : X → Spectrum}
    {u : X → ℝ} (hν : Continuous ν) (hu : Continuous u) (n : ℕ) :
    Continuous (fun x => meanB (ν x) (u x) n) := by
  have hw : Continuous (fun c : Frequency => (1 - (c : ℝ) ^ 2) * chebU (n - 1) c) :=
    (continuous_const.sub (continuous_subtype_val.pow 2)).mul
      ((continuous_chebU (n - 1)).comp continuous_subtype_val)
  exact (continuous_const.mul hu).mul ((continuous_avg hw).comp hν)

/-- Article: closedness of the infinite feasibility system. Proof: intersect all continuous slacks. -/
theorem isClosed_feasibleU {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {u t C : X → ℝ} (hν : Continuous ν) (hu : Continuous u)
    (ht : Continuous t) (hC : Continuous C) :
    IsClosed {x | FeasibleU (u x) (t x) (ν x) (C x)} := by
  have hG := isClosed_le hC.abs (continuous_meanG hν hu)
  have hlag : IsClosed {x | ∀ n : ℕ, 1 ≤ n →
      0 ≤ meanA (ν x) (u x) (t x) n - meanB (ν x) (u x) n +
        C x * Real.sinh (n * t x) ∧
      0 ≤ meanA (ν x) (u x) (t x) n + meanB (ν x) (u x) n -
        C x * Real.sinh (n * t x)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro _hn
    have ha := continuous_meanA hν hu ht n
    have hb := continuous_meanB hν hu n
    have hc : Continuous (fun x => C x * Real.sinh (n * t x)) :=
      hC.mul (Real.continuous_sinh.comp (continuous_const.mul ht))
    exact (isClosed_le continuous_const ((ha.sub hb).add hc)).inter
      (isClosed_le continuous_const ((ha.add hb).sub hc))
  exact hG.inter hlag

/-- Article: parameter closedness in (v,t). Proof: compose the closed u system with sinh. -/
theorem isClosed_feasible {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {v t C : X → ℝ} (hν : Continuous ν) (hv : Continuous v)
    (ht : Continuous t) (hC : Continuous C) :
    IsClosed {x | Feasible (v x) (t x) (ν x) (C x)} :=
  isClosed_feasibleU hν (Real.continuous_sinh.comp hv) ht hC

/-- Article: compactness for fixed parameters. Proof: C∈[-1,1] and the spectrum space is compact. -/
theorem isCompact_feasible_pairs (v t : ℝ) :
    IsCompact {p : Spectrum × ℝ | Feasible v t p.1 p.2} := by
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))).of_isClosed_subset
    (isClosed_feasible continuous_fst continuous_const continuous_const continuous_snd)
  intro p hp
  exact ⟨Set.mem_univ _, abs_le.mp hp.abs_C_le_one⟩

/-- Article: compactness with moving parameters. Proof: the complete constraint graph is closed. -/
theorem isCompact_feasible_over {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    IsCompact {p : (ℝ × ℝ) × (Spectrum × ℝ) |
      p.1 ∈ K ∧ Feasible p.1.1 p.1.2 p.2.1 p.2.2} := by
  have hcl := (hK.isClosed.preimage continuous_fst).inter
    (isClosed_feasible continuous_snd.fst continuous_fst.fst
      continuous_fst.snd continuous_snd.snd)
  apply (hK.prod (isCompact_univ.prod (isCompact_Icc : IsCompact
    (Set.Icc (-1 : ℝ) 1)))).of_isClosed_subset hcl
  intro p hp
  exact ⟨hp.1, Set.mem_univ _, abs_le.mp hp.2.abs_C_le_one⟩

/-- Article: zero twist is always feasible. Use: nonemptiness before defining a maximum.
Proof: the endpoint atom c=1 has all g, a, b, and C identically zero. -/
theorem feasible_zero (t : ℝ) : ∃ ν : Spectrum, Feasible 0 t ν 0 := by
  let c : Frequency := ⟨1, by norm_num⟩
  let ν : Spectrum := ⟨Measure.dirac c, by infer_instance⟩
  refine ⟨ν, ?_⟩
  have havg (f : Frequency → ℝ) : avg ν f = f c := by
    simp [avg, ν]
  simp only [Feasible, Real.sinh_zero, FeasibleU, meanG, meanA, meanB, havg]
  norm_num [c]

/-- Article: feasible twists. Use: a closed bounded set whose maximum defines V(t). -/
def twists (t : ℝ) : Set ℝ := {v | ∃ ν C, Feasible v t ν C}

/-- Article: boundedness of all feasible twists. Proof: the integrated minimizer constraint. -/
theorem twists_subset (t : ℝ) : twists t ⊆ Set.Icc (-Real.arsinh 1) (Real.arsinh 1) := by
  rintro v ⟨ν, C, h⟩
  exact abs_le.mp h.abs_v_le_arsinh_one

/-- Article: compactness of the twist set. Proof: compact graph over its a priori bounded interval. -/
theorem isCompact_twists (t : ℝ) : IsCompact (twists t) := by
  let K := Set.Icc (-Real.arsinh 1) (Real.arsinh 1) ×ˢ ({t} : Set ℝ)
  have hc := isCompact_feasible_over (isCompact_Icc.prod isCompact_singleton : IsCompact K)
  have heq : twists t = (fun p : (ℝ × ℝ) × (Spectrum × ℝ) => p.1.1) ''
      {p | p.1 ∈ K ∧ Feasible p.1.1 p.1.2 p.2.1 p.2.2} := by
    ext v
    constructor
    · rintro ⟨ν, C, h⟩
      exact ⟨((v, t), (ν, C)), ⟨⟨twists_subset t ⟨ν, C, h⟩, rfl⟩, h⟩, rfl⟩
    · rintro ⟨⟨⟨v', t'⟩, ν, C⟩, hp, rfl⟩
      have ht' : t' = t := hp.1.2
      exact ⟨ν, C, by simpa [ht'] using hp.2⟩
  rw [heq]
  exact hc.image continuous_fst.fst



/-- Article: zero twist. Proof: the explicit endpoint spectrum. -/
theorem zero_mem_twists (t : ℝ) : 0 ∈ twists t := by
  obtain ⟨ν, h⟩ := feasible_zero t
  exact ⟨ν, 0, h⟩

/-- Article: maximal feasible twist V(t). Use: an attained maximum, not an assumed supremum. -/
def V (t : ℝ) : ℝ := sSup (twists t)

/-- Article: existence of V. Proof: the nonempty twist set is compact. -/
theorem isGreatest_V (t : ℝ) : IsGreatest (twists t) (V t) :=
  (isCompact_twists t).isGreatest_sSup ⟨0, zero_mem_twists t⟩

/-- Article: feasibility at the boundary. Proof: compactness attains the supremum. -/
theorem V_mem (t : ℝ) : ∃ ν C, Feasible (V t) t ν C := (isGreatest_V t).1

/-- Article: V is nonnegative. Proof: zero is feasible. -/
theorem V_nonneg (t : ℝ) : 0 ≤ V t := (isGreatest_V t).2 (zero_mem_twists t)

/-- Article: uniform twist bound. Proof: apply the minimizer constraint at the maximum. -/
theorem V_le_arsinh_one (t : ℝ) : V t ≤ Real.arsinh 1 :=
  (twists_subset t (isGreatest_V t).1).2

/-- Article: t symmetry of the full twist set. Proof: negate the value constant. -/
theorem twists_neg (t : ℝ) : twists (-t) = twists t := by
  ext v
  constructor
  · rintro ⟨ν, C, h⟩
    refine ⟨ν, -C, ?_⟩
    simpa only [neg_neg] using (feasible_neg_t_iff v (-t) C ν).mpr h
  · rintro ⟨ν, C, h⟩
    exact ⟨ν, -C, (feasible_neg_t_iff v t C ν).mpr h⟩

/-- Article: V is even. Proof: t and -t have exactly the same feasible twist set. -/
theorem V_even (t : ℝ) : V (-t) = V t := by rw [V, twists_neg, V]

/-- Article: feasible twists form an interval, including zero. Proof: symmetry and monotonicity. -/
theorem mem_twists_iff (v t : ℝ) : v ∈ twists t ↔ |v| ≤ V t := by
  constructor
  · rintro ⟨ν, C, h⟩
    rw [abs_le]
    refine ⟨?_, (isGreatest_V t).2 ⟨ν, C, h⟩⟩
    have hn : -v ≤ V t := (isGreatest_V t).2
      ⟨ν, -C, (feasible_neg_v_iff v t C ν).mpr h⟩
    linarith
  · intro hv
    obtain ⟨ν, C, h⟩ := V_mem t
    obtain ⟨C', h'⟩ := h.mono (abs_nonneg v) hv
    by_cases hv0 : 0 ≤ v
    · exact ⟨ν, C', by simpa only [abs_of_nonneg hv0] using h'⟩
    · refine ⟨ν, -C', ?_⟩
      have hs := (feasible_neg_v_iff |v| t C' ν).mpr h'
      simpa only [abs_of_neg (lt_of_not_ge hv0), neg_neg] using hs

/-- Article: the set of feasible v is exactly [-V(t),V(t)]. Proof: the absolute value criterion. -/
theorem twists_eq_Icc (t : ℝ) : twists t = Set.Icc (-V t) (V t) := by
  ext v
  rw [mem_twists_iff, abs_le]
  rfl

end polyak.Spectral
