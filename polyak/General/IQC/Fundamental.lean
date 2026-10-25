import polyak.General.Roots
import polyak.General.IQC.Convolution
import Mathlib.Algebra.Ring.GeomSum

/-! Appendix D: the stable second order filter, including repeated and zero
roots. The impulse coefficients are controlled by the convolution of the
two geometric root sequences, so no distinct-root assumption is needed. -/
noncomputable section
namespace polyak.General.IQC
open Finset

def fundamental (a b : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a
  | n+2 => a*fundamental a b (n+1)-b*fundamental a b n

def rootSum (z w : ℂ) (n : ℕ) : ℂ := ∑ j∈range (n+1),z^j*w^(n-j)

theorem rootSum_step (z w : ℂ) (n : ℕ) :
    rootSum z w (n+1)=w^(n+1)+z*rootSum z w n := by
  rw [rootSum,sum_range_succ']
  simp only [pow_zero,one_mul,Nat.sub_zero]
  rw [rootSum,mul_sum]
  rw [add_comm _ (w^(n+1))]
  apply congrArg (fun s : ℂ => w^(n+1)+s)
  apply sum_congr rfl
  intro j hj
  rw [show n+1-(j+1)=n-j by omega,pow_succ]
  ring

theorem rootSum_recurrence (z w : ℂ) (n : ℕ) :
    rootSum z w (n+2)=(z+w)*rootSum z w (n+1)-(z*w)*rootSum z w n := by
  have h0:=rootSum_step z w n
  have h1:=rootSum_step z w (n+1)
  rw [show n+2=(n+1)+1 by omega,h1,h0,pow_succ]
  ring

theorem fundamental_complex {a b : ℝ} {z w : ℂ}
    (ha : z+w=(a : ℂ)) (hb : z*w=(b : ℂ)) (n : ℕ) :
    (fundamental a b n : ℂ)=rootSum z w n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [fundamental,rootSum]
  | one => simpa [fundamental,rootSum,sum_range_succ,add_comm] using ha.symm
  | more n ih ih1 =>
    rw [fundamental,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_mul,
      ih,ih1,←ha,←hb,rootSum_recurrence]

theorem rootSum_norm_le (z w : ℂ) (n : ℕ) :
    ‖rootSum z w n‖≤((n : ℝ)+1)*(max ‖z‖ ‖w‖)^n := by
  let q:=max ‖z‖ ‖w‖
  have hq : 0≤q:=(norm_nonneg z).trans (le_max_left _ _)
  calc
    _≤∑ j∈range (n+1),‖z^j*w^(n-j)‖:=norm_sum_le _ _
    _≤∑ _j∈range (n+1),q^n:=by
      apply sum_le_sum
      intro j hj
      rw [norm_mul,norm_pow,norm_pow]
      have he : q^j*q^(n-j)=q^n:=by
        rw [←pow_add,show j+(n-j)=n by have hh:=mem_range.mp hj; omega]
      rw [←he]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
        (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _) (by positivity) (by positivity)
    _=_:=by simp [q]

theorem fundamental_summable {a b : ℝ} {z w : ℂ}
    (ha : z+w=(a : ℂ)) (hb : z*w=(b : ℂ)) (hz : ‖z‖<1) (hw : ‖w‖<1) :
    Summable (fun n => |fundamental a b n|) := by
  let q:=max ‖z‖ ‖w‖
  have hq0 : 0≤q:=(norm_nonneg z).trans (le_max_left _ _)
  have hq1 : q<1:=max_lt hz hw
  have hnq : ‖q‖<1:=by rwa [Real.norm_eq_abs,abs_of_nonneg hq0]
  have hs : Summable (fun n : ℕ => (n : ℝ)*q^n):=by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnq
  have hg:=summable_geometric_of_lt_one hq0 hq1
  have hsum : Summable (fun n : ℕ => ((n : ℝ)+1)*q^n):=by
    simpa only [add_mul,one_mul] using hs.add hg
  apply hsum.of_nonneg_of_le (fun _ => abs_nonneg _)
  intro n
  have hh:=rootSum_norm_le z w n
  rw [←fundamental_complex ha hb n,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

theorem fundamental_summable_of_roots {a b : ℝ}
    (hstable : ∀ z : ℂ,z^2-(a : ℂ)*z+(b : ℂ)=0 → ‖z‖<1) :
    Summable (fun n => |fundamental a b n|) := by
  obtain ⟨z,hz⟩:=Dynamics.exists_complex_quadratic_root a b
  let w:=(a : ℂ)-z
  have ha : z+w=(a : ℂ):=by dsimp [w]; ring
  have hb : z*w=(b : ℂ):=by dsimp [w]; linear_combination -hz
  have hw : w^2-(a : ℂ)*w+(b : ℂ)=0:=by dsimp [w]; linear_combination hz
  exact fundamental_summable ha hb (hstable z hz) (hstable w hw)

end polyak.General.IQC
