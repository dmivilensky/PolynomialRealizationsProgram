import polyak.Waves.Interpolation
import polyak.Waves.Dynamics
import polyak.Spectral.Compact

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

namespace polyak.Spectral

/-- Article: continuity of spectral averaging with moving integrands and measures.
Proof: split the variation into a fixed continuous integrand against the moving
measure and a uniform-norm error; probability mass is exactly one. -/
theorem continuous_integral_family {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {f : X → C(Frequency, ℝ)}
    (hν : Continuous ν) (hf : Continuous f) :
    Continuous (fun x => ∫ c, f x c ∂ν x) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  have herror : Filter.Tendsto
      (fun x => ∫ c, (f x - f x₀) c ∂ν x) (𝓝 x₀) (𝓝 0) := by
    apply squeeze_zero_norm
    · intro x
      have hb := norm_integral_le_of_norm_le_const
        (μ := (ν x : Measure Frequency))
        (Filter.Eventually.of_forall (fun c => (f x - f x₀).norm_coe_le_norm c))
      simpa using hb
    · have hn : Continuous (fun x => ‖f x - f x₀‖) := (hf.sub continuous_const).norm
      simpa using hn.tendsto x₀
  have hfixed := ((ProbabilityMeasure.continuous_integral_continuousMap (f x₀)).comp hν).tendsto x₀
  have hsum := herror.add hfixed
  simp only [zero_add] at hsum
  change Filter.Tendsto (fun x => ∫ c, f x c ∂ν x) (𝓝 x₀) (𝓝 (∫ c, f x₀ c ∂ν x₀))
  convert hsum using 1
  · funext x
    dsimp only [Function.comp_apply]
    rw [← integral_add]
    · congr 1
      funext c
      simp
    · exact integrable_continuous (ν x) (f x - f x₀).continuous
    · exact integrable_continuous (ν x) (f x₀).continuous
  · rfl

/-- Article: joint continuity of the minimizer slack for a general continuous
multiplier. Proof: the squared complex norm is continuous on the compact carrier. -/
theorem continuous_spectrumG {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {m : X → C(Frequency, ℂ)}
    (hν : Continuous ν) (hm : Continuous m) :
    Continuous (fun x => Waves.spectrumG (ν x) (m x)) := by
  let f : X → C(Frequency, ℝ) := fun x =>
    ⟨fun c => 1 - Complex.normSq (m x c), by fun_prop⟩
  apply continuous_integral_family hν (f := f)
  apply ContinuousMap.continuous_of_continuous_uncurry
  have heval : Continuous (fun p : X × Frequency => m p.1 p.2) := by
    exact continuous_eval.comp ((hm.comp continuous_fst).prodMk continuous_snd)
  exact continuous_const.sub (Complex.continuous_normSq.comp heval)

/-- Article: joint continuity of every symmetric lag slack for arbitrary tuning.
Proof: compact-carrier continuity and joint continuous spectral averaging. -/
theorem continuous_spectrumA {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {m : X → C(Frequency, ℂ)} {t : X → ℝ}
    (hν : Continuous ν) (hm : Continuous m) (ht : Continuous t) (n : ℕ) :
    Continuous (fun x => Waves.spectrumA (ν x) (m x) (t x) n) := by
  let f : X → C(Frequency, ℝ) := fun x =>
    ⟨fun c => (1 - Complex.normSq (m x c)) *
      (Real.cosh (n * t x) - Real.cos (n * Real.arccos c)), by fun_prop⟩
  apply continuous_integral_family hν (f := f)
  apply ContinuousMap.continuous_of_continuous_uncurry
  have heval : Continuous (fun p : X × Frequency => m p.1 p.2) := by
    exact continuous_eval.comp ((hm.comp continuous_fst).prodMk continuous_snd)
  exact (continuous_const.sub (Complex.continuous_normSq.comp heval)).mul
    ((Real.continuous_cosh.comp (continuous_const.mul (ht.comp continuous_fst))).sub
      (Real.continuous_cos.comp (continuous_const.mul
        (Real.continuous_arccos.comp (continuous_subtype_val.comp continuous_snd)))))

/-- Article: joint continuity of every skew lag slack for arbitrary tuning.
Proof: compact-carrier continuity and joint continuous spectral averaging. -/
theorem continuous_spectrumB {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {m : X → C(Frequency, ℂ)}
    (hν : Continuous ν) (hm : Continuous m) (n : ℕ) :
    Continuous (fun x => Waves.spectrumB (ν x) (m x) n) := by
  let f : X → C(Frequency, ℝ) := fun x =>
    ⟨fun c => 2 * (m x c).im * Real.sin (n * Real.arccos c), by fun_prop⟩
  apply continuous_integral_family hν (f := f)
  apply ContinuousMap.continuous_of_continuous_uncurry
  have heval : Continuous (fun p : X × Frequency => m p.1 p.2) := by
    exact continuous_eval.comp ((hm.comp continuous_fst).prodMk continuous_snd)
  exact (continuous_const.mul (Complex.continuous_im.comp heval)).mul
    (Real.continuous_sin.comp (continuous_const.mul
      (Real.continuous_arccos.comp (continuous_subtype_val.comp continuous_snd))))

/-- Article: every general-tuning minimizer slack is at most one.
Proof: integrate 1−|m|²≤1 against a probability measure. -/
theorem spectrumG_le_one (ν : Spectrum) (m : C(Frequency, ℂ)) :
    Waves.spectrumG ν m ≤ 1 := by
  have h := integral_mono (integrable_continuous ν (show Continuous
      (fun c => 1 - Complex.normSq (m c)) by fun_prop))
    (integrable_const (1 : ℝ))
    (fun c => sub_le_self (1 : ℝ) (Complex.normSq_nonneg (m c)))
  simpa [Waves.spectrumG] using h

/-- Article: uniform boundedness of the value constant under arbitrary tuning.
Proof: the minimizer constraint and the unit probability mass. -/
theorem abs_C_le_one_of_mixtureFeasible {ν : Spectrum} {m : C(Frequency, ℂ)} {C t : ℝ}
    (h : Waves.MixtureFeasible ν m C t) : |C| ≤ 1 :=
  h.1.trans (spectrumG_le_one ν m)

/-- Article: general tuning feasibility is closed jointly in all continuous
parameters and the weak topology of probability spectra.
Proof: every lag gives two closed continuous inequalities. -/
theorem isClosed_mixtureFeasible {X : Type*} [TopologicalSpace X]
    {ν : X → Spectrum} {m : X → C(Frequency, ℂ)} {C t : X → ℝ}
    (hν : Continuous ν) (hm : Continuous m) (hC : Continuous C) (ht : Continuous t) :
    IsClosed {x | Waves.MixtureFeasible (ν x) (m x) (C x) (t x)} := by
  have hG := isClosed_le hC.abs (continuous_spectrumG hν hm)
  have hlag : IsClosed {x | ∀ n : ℕ, 1 ≤ n →
      0 ≤ Waves.spectrumA (ν x) (m x) (t x) n - Waves.spectrumB (ν x) (m x) n +
        C x * Real.sinh (n * t x) ∧
      0 ≤ Waves.spectrumA (ν x) (m x) (t x) n + Waves.spectrumB (ν x) (m x) n -
        C x * Real.sinh (n * t x)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro _hn
    have ha := continuous_spectrumA hν hm ht n
    have hb := continuous_spectrumB hν hm n
    have hc : Continuous (fun x => C x * Real.sinh (n * t x)) :=
      hC.mul (Real.continuous_sinh.comp (continuous_const.mul ht))
    exact (isClosed_le continuous_const ((ha.sub hb).add hc)).inter
      (isClosed_le continuous_const ((ha.add hb).sub hc))
  exact hG.inter hlag

/-- Article: weak compactness for every fixed general tuning and exponent.
Proof: feasibility is a closed subset of probability spectra times [−1,1]. -/
theorem isCompact_mixtureFeasible_pairs (m : C(Frequency, ℂ)) (t : ℝ) :
    IsCompact {p : Spectrum × ℝ | Waves.MixtureFeasible p.1 m p.2 t} := by
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))).of_isClosed_subset
    (isClosed_mixtureFeasible continuous_fst continuous_const continuous_snd continuous_const)
  intro p hp
  exact ⟨Set.mem_univ _, abs_le.mp (abs_C_le_one_of_mixtureFeasible hp)⟩

/-- Article: weak compactness of the full constraint graph over a compact
parameter range, for arbitrary continuously varying multipliers and exponents.
Proof: close every lag and apply the uniform bound |C|≤1. -/
theorem isCompact_mixtureFeasible_over {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) {m : X → C(Frequency, ℂ)} {t : X → ℝ}
    (hm : Continuous m) (ht : Continuous t) :
    IsCompact {p : X × (Spectrum × ℝ) | p.1 ∈ K ∧
      Waves.MixtureFeasible p.2.1 (m p.1) p.2.2 (t p.1)} := by
  have hcl := (hK.isClosed.preimage continuous_fst).inter
    (isClosed_mixtureFeasible continuous_snd.fst (hm.comp continuous_fst)
      continuous_snd.snd (ht.comp continuous_fst))
  apply (hK.prod (isCompact_univ.prod (isCompact_Icc : IsCompact
    (Set.Icc (-1 : ℝ) 1)))).of_isClosed_subset hcl
  intro p hp
  exact ⟨hp.1, Set.mem_univ _, abs_le.mp (abs_C_le_one_of_mixtureFeasible hp.2)⟩

/-- Article: continuity of the genuine arbitrary-tuning multiplier, including
moving tuning parameters. Use: the general compactness theorem applies to the
actual heavy-ball formula wherever B is nonzero. -/
theorem continuous_multiplierMap {X : Type*} [TopologicalSpace X]
    {A B β t : X → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hβ : Continuous β) (ht : Continuous t) (hB0 : ∀ x, B x ≠ 0) :
    Continuous (fun x => Waves.multiplierMap (A x) (B x) (β x) (t x)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : X × Frequency =>
    Waves.multiplier (A p.1) (B p.1) (β p.1) (t p.1) (Real.arccos p.2))
  have hz : Continuous (fun p : X × Frequency => Waves.z (t p.1) (Real.arccos p.2)) := by
    unfold Waves.z
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (ht.comp continuous_fst)).add
        ((Complex.continuous_ofReal.comp
          (Real.continuous_arccos.comp (continuous_subtype_val.comp continuous_snd))).mul
            continuous_const))
  have hβ' := Complex.continuous_ofReal.comp (hβ.comp (continuous_fst : Continuous (Prod.fst : X × Frequency → X)))
  have hA' := Complex.continuous_ofReal.comp (hA.comp (continuous_fst : Continuous (Prod.fst : X × Frequency → X)))
  have hB' := Complex.continuous_ofReal.comp (hB.comp (continuous_fst : Continuous (Prod.fst : X × Frequency → X)))
  exact ((hz.add (hβ'.div hz (fun p => Complex.exp_ne_zero _))).sub hA').div hB'
    (fun p => Complex.ofReal_ne_zero.mpr (hB0 p.1))

/-- Article: arbitrary-tuning compactness with the actual multiplier and moving
exponent. Proof: continuity of the multiplier and the general compact graph. -/
theorem isCompact_generalTuning_over {K : Set ℝ} (hK : IsCompact K)
    (A B β : ℝ) (hB : B ≠ 0) :
    IsCompact {p : ℝ × (Spectrum × ℝ) | p.1 ∈ K ∧
      Waves.MixtureFeasible p.2.1 (Waves.multiplierMap A B β p.1) p.2.2 p.1} := by
  have hm : Continuous (fun t : ℝ => Waves.multiplierMap A B β t) :=
    continuous_multiplierMap (A := fun _ : ℝ => A) (B := fun _ => B)
      (β := fun _ => β) (t := id) continuous_const continuous_const continuous_const
      continuous_id (fun _ => hB)
  exact isCompact_mixtureFeasible_over (m := fun t : ℝ => Waves.multiplierMap A B β t)
    (t := id) hK hm continuous_id

end polyak.Spectral
