import LeanCert.Core.IntervalRat.TrigReduced
import LeanCert.Engine.Eval.Core
import polyak.Numerics.KernelDecide

/-! Rational proposals enclose actual trigonometric constants by the proved
Taylor remainder and the proved interval for pi. No computed real value is
accepted as an axiom. -/
namespace polyak.CertifiedExamples.Trigonometry
open LeanCert.Core LeanCert.Engine

def piTight : IntervalRat :=
  ⟨314159265358979323846/100000000000000000000,
   314159265358979323847/100000000000000000000,by norm_num⟩

theorem pi_mem : Real.pi ∈ piTight := by
  rw [IntervalRat.mem_def]
  constructor
  · have h := Real.pi_gt_d20
    norm_num [piTight] at *
    exact h.le
  · have h := Real.pi_lt_d20
    norm_num [piTight] at *
    exact h.le

def angleInterval (a : ℚ) : IntervalRat :=
  IntervalRat.mul (IntervalRat.singleton a) piTight

theorem angle_mem (a : ℚ) : (a : ℝ)*Real.pi ∈ angleInterval a :=
  IntervalRat.mem_mul (IntervalRat.mem_singleton a) pi_mem

def reduced (a : ℚ) : ℚ := if 1<a then a-2 else a

theorem sin_reduced (a : ℚ) :
    Real.sin (((reduced a : ℚ) : ℝ)*Real.pi)=Real.sin ((a : ℝ)*Real.pi) := by
  unfold reduced
  split_ifs with h
  · have he : (((a-2:ℚ):ℝ)*Real.pi)=(a:ℝ)*Real.pi-2*Real.pi := by push_cast; ring
    rw [he,Real.sin_sub_two_pi]
  · rfl

theorem cos_reduced (a : ℚ) :
    Real.cos (((reduced a : ℚ) : ℝ)*Real.pi)=Real.cos ((a : ℝ)*Real.pi) := by
  unfold reduced
  split_ifs with h
  · have he : (((a-2:ℚ):ℝ)*Real.pi)=(a:ℝ)*Real.pi-2*Real.pi := by push_cast; ring
    rw [he,Real.cos_sub_two_pi]
  · rfl

def sinEnclosure (a : ℚ) (n : ℕ) : IntervalRat :=
  IntervalRat.sinComputable (angleInterval (reduced a)) n

def cosEnclosure (a : ℚ) (n : ℕ) : IntervalRat :=
  IntervalRat.cosComputable (angleInterval (reduced a)) n

theorem sin_mem (a : ℚ) (n : ℕ) :
    Real.sin ((a : ℝ)*Real.pi) ∈ sinEnclosure a n :=
  by rw [← sin_reduced a]; exact IntervalRat.mem_sinComputable (angle_mem (reduced a)) n

theorem cos_mem (a : ℚ) (n : ℕ) :
    Real.cos ((a : ℝ)*Real.pi) ∈ cosEnclosure a n :=
  by rw [← cos_reduced a]; exact IntervalRat.mem_cosComputable (angle_mem (reduced a)) n

theorem sin_bounds (a : ℚ) (n : ℕ) (lo hi : ℚ)
    (h : lo ≤ (sinEnclosure a n).lo ∧ (sinEnclosure a n).hi ≤ hi) :
    (lo : ℝ) ≤ Real.sin ((a : ℝ)*Real.pi) ∧ Real.sin ((a : ℝ)*Real.pi) ≤ hi := by
  have hm := sin_mem a n
  rw [IntervalRat.mem_def] at hm
  have hl : (lo : ℝ) ≤ ((sinEnclosure a n).lo : ℝ) := by exact_mod_cast h.1
  have hh : ((sinEnclosure a n).hi : ℝ) ≤ (hi : ℝ) := by exact_mod_cast h.2
  exact ⟨hl.trans hm.1,hm.2.trans hh⟩

theorem cos_bounds (a : ℚ) (n : ℕ) (lo hi : ℚ)
    (h : lo ≤ (cosEnclosure a n).lo ∧ (cosEnclosure a n).hi ≤ hi) :
    (lo : ℝ) ≤ Real.cos ((a : ℝ)*Real.pi) ∧ Real.cos ((a : ℝ)*Real.pi) ≤ hi := by
  have hm := cos_mem a n
  rw [IntervalRat.mem_def] at hm
  have hl : (lo : ℝ) ≤ ((cosEnclosure a n).lo : ℝ) := by exact_mod_cast h.1
  have hh : ((cosEnclosure a n).hi : ℝ) ≤ (hi : ℝ) := by exact_mod_cast h.2
  exact ⟨hl.trans hm.1,hm.2.trans hh⟩

end polyak.CertifiedExamples.Trigonometry
