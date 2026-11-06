import nesterov.Spectral.Feasibility

/-!
Article: Appendix A, weak compactness for arbitrary tuning.
Use: closure of every lag constraint for changing continuous multipliers,
growth exponents, spectral probability measures, and value constants.
Proof: joint continuity of integration against probability measures, followed
by closed intersections in a compact probability space.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace nesterov.Spectral


abbrev continuous_integral_family := @polyak.Spectral.continuous_integral_family

theorem continuous_meanG {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {m : X → SymbolPair}
    (hν : Continuous ν) (hu : Continuous (fun x => (m x).u))
    (hp : Continuous (fun x => (m x).p)) :
    Continuous (fun x => meanG (ν x) (m x)) := by
  apply polyak.Spectral.continuous_integral_family hν
    (f := fun x => ⟨g (m x), continuous_g (m x)⟩)
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hu' := continuous_eval.comp ((hu.comp continuous_fst).prodMk continuous_snd)
  have hp' := continuous_eval.comp ((hp.comp continuous_fst).prodMk continuous_snd)
  exact (Complex.continuous_normSq.comp hu').sub (Complex.continuous_normSq.comp hp')

theorem continuous_meanA {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {m : X → SymbolPair} {t : X → ℝ}
    (hν : Continuous ν) (hu : Continuous (fun x => (m x).u))
    (hp : Continuous (fun x => (m x).p)) (ht : Continuous t) (n : ℕ) :
    Continuous (fun x => meanA (ν x) (m x) (t x) n) := by
  apply polyak.Spectral.continuous_integral_family hν
    (f := fun x => ⟨lagA (m x) (t x) n, continuous_lagA (m x) (t x) n⟩)
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hu' := continuous_eval.comp ((hu.comp continuous_fst).prodMk continuous_snd)
  have hp' := continuous_eval.comp ((hp.comp continuous_fst).prodMk continuous_snd)
  exact ((Complex.continuous_normSq.comp hu').sub (Complex.continuous_normSq.comp hp')).mul
    ((Real.continuous_cosh.comp (continuous_const.mul (ht.comp continuous_fst))).sub
      (Real.continuous_cos.comp (continuous_const.mul
        (Real.continuous_arccos.comp (continuous_subtype_val.comp continuous_snd)))))

theorem continuous_meanB {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {m : X → SymbolPair}
    (hν : Continuous ν) (hu : Continuous (fun x => (m x).u))
    (hp : Continuous (fun x => (m x).p)) (n : ℕ) :
    Continuous (fun x => meanB (ν x) (m x) n) := by
  apply polyak.Spectral.continuous_integral_family hν
    (f := fun x => ⟨lagB (m x) n, continuous_lagB (m x) n⟩)
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hu' := continuous_eval.comp ((hu.comp continuous_fst).prodMk continuous_snd)
  have hp' := continuous_eval.comp ((hp.comp continuous_fst).prodMk continuous_snd)
  exact (continuous_const.mul (Complex.continuous_im.comp (hp'.mul hu'.star))).mul
    (Real.continuous_sin.comp (continuous_const.mul
      (Real.continuous_arccos.comp (continuous_subtype_val.comp continuous_snd))))

/-- Article: general tuning feasibility is closed jointly in all continuous
parameters and the weak topology of probability spectra.
Proof: every lag gives two closed continuous inequalities. -/
theorem isClosed_feasible {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {m : X → SymbolPair} {C t : X → ℝ}
    (hν : Continuous ν) (hu : Continuous (fun x => (m x).u)) (hp : Continuous (fun x => (m x).p)) (hC : Continuous C) (ht : Continuous t) :
    IsClosed {x | Feasible (m x) (t x) (ν x) (C x)} := by
  have hG := isClosed_le hC.abs (continuous_meanG hν hu hp)
  have hlag : IsClosed {x | ∀ n : ℕ, 1 ≤ n →
      0 ≤ meanA (ν x) (m x) (t x) n - meanB (ν x) (m x) n +
        C x * Real.sinh (n * t x) ∧
      0 ≤ meanA (ν x) (m x) (t x) n + meanB (ν x) (m x) n -
        C x * Real.sinh (n * t x)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro _hn
    have ha := continuous_meanA hν hu hp ht n
    have hb := continuous_meanB hν hu hp n
    have hc : Continuous (fun x => C x * Real.sinh (n * t x)) :=
      hC.mul (Real.continuous_sinh.comp (continuous_const.mul ht))
    exact (isClosed_le continuous_const ((ha.sub hb).add hc)).inter
      (isClosed_le continuous_const ((ha.add hb).sub hc))
  exact hG.inter hlag

/-- Article: weak compactness for every fixed general tuning and exponent.
Proof: feasibility is a closed subset of probability spectra times [−1,1]. -/
theorem isCompact_feasible_pairs (m : SymbolPair) (t : ℝ) :
    IsCompact {p : Spectrum × ℝ | Feasible m t p.1 p.2} := by
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Set.Icc (-‖m.u‖ ^ 2 : ℝ) (‖m.u‖ ^ 2)))).of_isClosed_subset
    (isClosed_feasible continuous_fst continuous_const continuous_const continuous_snd continuous_const)
  intro p hp
  exact ⟨Set.mem_univ _, abs_le.mp (hp.abs_C_le)⟩


/-- The complete feasible graph is compact over any compact parameter set.
The unrestricted value constant is bounded by the query amplitude, uniformly on that set. -/
theorem isCompact_feasible_over {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) {m : X → SymbolPair} {t : X → ℝ}
    (hu : Continuous (fun x => (m x).u)) (hp : Continuous (fun x => (m x).p))
    (ht : Continuous t) :
    IsCompact {p : X × (Spectrum × ℝ) | p.1 ∈ K ∧
      Feasible (m p.1) (t p.1) p.2.1 p.2.2} := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hu.norm.pow 2).continuousOn
  have hcl := (hK.isClosed.preimage continuous_fst).inter
    (isClosed_feasible continuous_snd.fst (hu.comp continuous_fst)
      (hp.comp continuous_fst) continuous_snd.snd (ht.comp continuous_fst))
  apply (hK.prod (isCompact_univ.prod (isCompact_Icc : IsCompact
    (Set.Icc (-B : ℝ) B)))).of_isClosed_subset hcl
  intro p hp
  refine ⟨hp.1, Set.mem_univ _, abs_le.mp (hp.2.abs_C_le.trans ?_)⟩
  exact hB (Set.mem_image_of_mem _ hp.1)

end nesterov.Spectral
