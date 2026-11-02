import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Uniform

/-!
Article: main_krylov, lem:xr-local, genuine finite oracle perturbations.
Use: a continuous data-only adaptive query program preserves its actual
finite query domain and observations under a uniformly small oracle
perturbation. Domains are conclusions obtained by induction, not query
bounds assumed in a native execution field.
Source: continuity at the actual reference transcript and finite induction.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
variable {E D : Type*} [NormedAddCommGroup E] [NormedAddCommGroup D]

/-- Actual chronological observations of a finite adaptive oracle rule. -/
def adaptiveTranscript (query : (k : ℕ) → (Fin k → D) → E) (oracle : E → D) :
    (k : ℕ) → Fin k → D
  | 0 => Fin.elim0
  | k + 1 => Fin.snoc (adaptiveTranscript query oracle k)
      (oracle (query k (adaptiveTranscript query oracle k)))

/-- The real next queried point, computed only from previous actual
observations, without any reference-trajectory input. -/
def adaptivePoint (query : (k : ℕ) → (Fin k → D) → E) (oracle : E → D) (k : ℕ) : E :=
  query k (adaptiveTranscript query oracle k)

/-- Uniformly small oracle errors preserve every actual finite query and
make the full true observed transcript arbitrarily close to its reference. -/
theorem finite_adaptive_oracle_stability
    (query : (k : ℕ) → (Fin k → D) → E) (reference : E → D) (hreference : Continuous reference)
    (U : Set E) (hU : IsOpen U) (N : ℕ)
    (hquery : ∀ k < N, ContinuousAt (query k) (adaptiveTranscript query reference k))
    (hpoints : ∀ k < N, adaptivePoint query reference k ∈ U)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ oracle : E → D,
      (∀ x ∈ U, ‖oracle x - reference x‖ ≤ epsilon) →
      (∀ k < N, adaptivePoint query oracle k ∈ U) ∧
        ‖adaptiveTranscript query oracle N - adaptiveTranscript query reference N‖ < delta := by
  induction N generalizing delta with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro oracle _
    constructor
    · intro k hk
      omega
    · have he : adaptiveTranscript query oracle 0 - adaptiveTranscript query reference 0 = 0 := by
        ext i
        exact Fin.elim0 i
      rwa [he, norm_zero]
  | succ N ih =>
    let data₀ := adaptiveTranscript query reference N
    have hq := hquery N (by omega)
    have hvalue : ContinuousAt (fun data : Fin N → D =>
        ‖reference (query N data) - reference (query N data₀)‖) data₀ :=
      ((hreference.continuousAt.comp hq).sub continuousAt_const).norm
    have hsmall : ∀ᶠ data in 𝓝 data₀,
        query N data ∈ U ∧ ‖reference (query N data) - reference (query N data₀)‖ < delta / 2 := by
      have hfirst : ∀ᶠ data in 𝓝 data₀, query N data ∈ U :=
        hq.preimage_mem_nhds (hU.mem_nhds (hpoints N (by omega)))
      have hsecond := hvalue.eventually (gt_mem_nhds (show
        ‖reference (query N data₀) - reference (query N data₀)‖ < delta / 2 by
          rw [sub_self, norm_zero]; positivity))
      exact hfirst.and hsecond
    obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp hsmall
    obtain ⟨epsilon₀, hepsilon₀, hstable⟩ := ih
      (fun k hk => hquery k (by omega)) (fun k hk => hpoints k (by omega))
      (min r (delta / 2)) (lt_min hr (by positivity))
    refine ⟨min epsilon₀ (delta / 2), lt_min hepsilon₀ (by positivity), ?_⟩
    intro oracle herror
    obtain ⟨hprevious, hhistory⟩ := hstable oracle
      (fun x hx => (herror x hx).trans (min_le_left _ _))
    have hdata : dist (adaptiveTranscript query oracle N) data₀ < r := by
      rw [dist_eq_norm]
      exact hhistory.trans_le (min_le_left _ _)
    have hcurrent := hlocal hdata
    have hnew : ‖oracle (adaptivePoint query oracle N) - reference (adaptivePoint query reference N)‖ < delta := by
      have he := herror _ hcurrent.1
      change ‖oracle (adaptivePoint query oracle N) - reference (adaptivePoint query oracle N)‖ ≤
        min epsilon₀ (delta / 2) at he
      have ht := norm_sub_le_norm_sub_add_norm_sub
        (oracle (adaptivePoint query oracle N)) (reference (adaptivePoint query oracle N))
        (reference (adaptivePoint query reference N))
      have hv := hcurrent.2
      change ‖reference (adaptivePoint query oracle N) - reference (adaptivePoint query reference N)‖ < delta / 2 at hv
      linarith [min_le_right epsilon₀ (delta / 2)]
    constructor
    · intro k hk
      by_cases he : k = N
      · subst k
        exact hcurrent.1
      · exact hprevious k (by omega)
    · apply (pi_norm_lt_iff hdelta).2
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change ‖oracle (query N (adaptiveTranscript query oracle N)) -
          reference (query N (adaptiveTranscript query reference N))‖ < delta at hnew
        simpa only [adaptiveTranscript, Pi.sub_apply, Fin.snoc_last] using hnew
      · have hh := (norm_le_pi_norm
          (adaptiveTranscript query oracle N - adaptiveTranscript query reference N) j).trans_lt hhistory
        have hb := hh.trans_le (min_le_right r (delta / 2))
        have hs : ‖(adaptiveTranscript query oracle N - adaptiveTranscript query reference N) j‖ < delta := by
          linarith
        simpa only [adaptiveTranscript, Pi.sub_apply, Fin.snoc_castSucc] using hs

/-- Every finite open branch containing the real reference transcript is
preserved by a genuinely small source-oracle perturbation. No branch
success is assumed on the perturbed execution. -/
theorem finite_adaptive_open_branch
    (query : (k : ℕ) → (Fin k → D) → E) (reference : E → D) (hreference : Continuous reference)
    (U : Set E) (hU : IsOpen U) (N : ℕ)
    (hquery : ∀ k < N, ContinuousAt (query k) (adaptiveTranscript query reference k))
    (hpoints : ∀ k < N, adaptivePoint query reference k ∈ U)
    (V : Set (Fin N → D)) (hV : V ∈ 𝓝 (adaptiveTranscript query reference N)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ oracle : E → D,
      (∀ x ∈ U, ‖oracle x - reference x‖ ≤ epsilon) →
      (∀ k < N, adaptivePoint query oracle k ∈ U) ∧ adaptiveTranscript query oracle N ∈ V := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨epsilon, hepsilon, hstable⟩ := finite_adaptive_oracle_stability query reference hreference U hU N
    hquery hpoints r hr
  refine ⟨epsilon, hepsilon, ?_⟩
  intro oracle herror
  obtain ⟨hqueries, hdata⟩ := hstable oracle herror
  refine ⟨hqueries, hsub ?_⟩
  simpa only [mem_ball, dist_eq_norm] using hdata

end
end krylov.XR
