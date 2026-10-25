import polyak.CertifiedExamples.Plateaus.Arithmetic
import polyak.Numerics.KernelDecide

/-! A rejecting enclosure check. Candidate endpoints carry no semantic
authority: the proved expression evaluator must fit inside them. -/
namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Core chebyshev2.Numerics

def enclosed {d : ℕ} (e : E d) (box : Fin d → IntervalRat) (target : IntervalRat) : Bool :=
  match e.enclose box with
  | none => false
  | some I => decide (target.lo≤I.lo ∧ I.hi≤target.hi)

theorem enclosed_sound {d : ℕ} (e : E d) (box : Fin d → IntervalRat) (target : IntervalRat)
    (hc : enclosed e box target=true) (v : Fin d → ℝ) (hv : ∀ i,v i∈box i) :
    e.value v∈target := by
  cases he : e.enclose box with
  | none => simp only [enclosed,he,Bool.false_eq_true] at hc
  | some I =>
    have hh : target.lo≤I.lo ∧ I.hi≤target.hi := by
      simpa only [enclosed,he,decide_eq_true_eq] using hc
    have hi := e.enclose_sound box he hv
    have hlo : (target.lo:ℝ)≤I.lo := by exact_mod_cast hh.1
    have hhi : (I.hi:ℝ)≤target.hi := by exact_mod_cast hh.2
    exact ⟨hlo.trans hi.1,hi.2.trans hhi⟩

end polyak.CertifiedExamples.Plateaus
