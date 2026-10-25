import polyak.General.IQC.Fundamental
import polyak.General.IQC.ConvolutionRecurrence
import polyak.Energy.Symbol

/-! Appendix D: the actual stable strictly proper heavy-ball plant.
All impulse estimates include repeated roots and a zero root. -/

namespace polyak.General.IQC
noncomputable section
open Finset

theorem scaled_roots_stable {A beta r : ℝ} (hbeta : 0 ≤ beta)
    (hr : rootRadius A beta < r) {z : ℂ}
    (hz : z^2-(A/r:ℝ)*z+(beta/r^2:ℝ)=0) : ‖z‖ < 1 := by
  have hr0 : 0 < r := (rootRadius_nonneg _ _).trans_lt hr
  have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr0
  have hroot : ((r:ℂ)*z)^2-(A:ℂ)*((r:ℂ)*z)+(beta:ℂ)=0 := by
    push_cast at hz
    field_simp [hrc] at hz
    linear_combination hz
  have hbound := (root_norm_le hbeta hroot).trans_lt hr
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0] at hbound
  nlinarith

def plantImpulse (A B beta r : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => (B/r)*fundamental (A/r) (beta/r^2) n

theorem plantImpulse_recurrence (A B beta r : ℝ) (n : ℕ) :
    plantImpulse A B beta r (n+2) =
      (A/r)*plantImpulse A B beta r (n+1)-(beta/r^2)*plantImpulse A B beta r n := by
  cases n with
  | zero => simp [plantImpulse,fundamental,mul_comm]
  | succ n => simp only [plantImpulse,fundamental]; ring

theorem fundamental_scaled_summable {A beta r : ℝ} (hbeta : 0 ≤ beta)
    (hr : rootRadius A beta < r) :
    Summable (fun n => |fundamental (A/r) (beta/r^2) n|) :=
  fundamental_summable_of_roots (fun _ hz => scaled_roots_stable hbeta hr hz)

theorem plantImpulse_summable {A B beta r : ℝ} (hbeta : 0 ≤ beta)
    (hr : rootRadius A beta < r) : Summable (fun n => |plantImpulse A B beta r n|) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [plantImpulse,abs_mul] using
    (fundamental_scaled_summable hbeta hr).mul_left |B/r|

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def stablePlant (A B beta r : ℝ) : (ℕ → E) →ₗ[ℝ] (ℕ → E) :=
  convolution (plantImpulse A B beta r)

theorem stablePlant_strictCausal (A B beta r : ℝ) :
    StrictCausal (stablePlant (E:=E) A B beta r) :=
  convolution_strictCausal rfl

theorem stablePlant_prefix_gain {A B beta r : ℝ} (hbeta : 0 ≤ beta)
    (hr : rootRadius A beta < r) (x : ℕ → E) (N : ℕ) :
    prefixNorm (stablePlant A B beta r x) N ≤
      (∑' n, |plantImpulse A B beta r n|)*prefixNorm x N :=
  convolution_prefix_gain (plantImpulse_summable hbeta hr) x N

@[simp] theorem stablePlant_zero (A B beta r : ℝ) (x : ℕ → E) :
    stablePlant A B beta r x 0 = 0 := by
  simp [stablePlant,plantImpulse]

theorem stablePlant_one (A B beta r : ℝ) (x : ℕ → E) :
    stablePlant A B beta r x 1 = (B/r) • x 0 := by
  simp [stablePlant,convolution_one,plantImpulse,fundamental]

theorem stablePlant_recurrence (A B beta r : ℝ) (x : ℕ → E) (n : ℕ) :
    stablePlant A B beta r x (n+2) =
      (A/r) • stablePlant A B beta r x (n+1) -
      (beta/r^2) • stablePlant A B beta r x n + (B/r) • x (n+1) := by
  have h := convolution_recurrence (plantImpulse_recurrence A B beta r) x n
  simpa only [stablePlant,plantImpulse,fundamental,mul_zero,mul_one,sub_zero,zero_smul,add_zero] using h

def zeroExtend (x : ℕ → E) (k : ℤ) : E := if 0 ≤ k then x k.toNat else 0

omit [NormedSpace ℝ E] in
@[simp] theorem zeroExtend_nat (x : ℕ → E) (k : ℕ) : zeroExtend x k=x k := by simp [zeroExtend]
omit [NormedSpace ℝ E] in
theorem zeroExtend_neg (x : ℕ → E) {k : ℤ} (hk : k<0) : zeroExtend x k=0 := by
  simp [zeroExtend,not_le.mpr hk]

end
end polyak.General.IQC
