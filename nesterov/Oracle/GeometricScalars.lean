import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! The concrete geometric sequences used for the deterministic oracle lower
bound, normalized to smoothness one and initial radius one. -/
namespace nesterov.Oracle.Geometric
noncomputable section
open Finset

def rho (s : ℝ) : ℝ := 1-s
def delta (s : ℝ) (i : ℕ) : ℝ := Real.sqrt (1-rho s^2)*rho s^i
def gamma (s : ℝ) (i : ℕ) : ℝ := s*delta s i

theorem rho_pos {s : ℝ} (hs : s<1) : 0<rho s := by unfold rho;linarith
theorem rho_lt_one {s : ℝ} (hs : 0<s) : rho s<1 := by unfold rho;linarith

theorem delta_pos {s : ℝ} (hs : 0<s) (hs1 : s<1) (i : ℕ) : 0<delta s i := by
  have hρ := rho_pos hs1
  have hρ1 := rho_lt_one hs
  unfold delta
  exact mul_pos (Real.sqrt_pos.mpr (by nlinarith)) (pow_pos hρ i)

theorem delta_sq {s : ℝ} (hs : 0<s) (hs1 : s<1) (i : ℕ) :
    delta s i^2=(1-rho s^2)*(rho s^2)^i := by
  unfold delta
  rw [mul_pow,Real.sq_sqrt (by nlinarith [rho_pos hs1,rho_lt_one hs])]
  have hp : (rho s^i)^2=(rho s^2)^i := by
    calc
      _=rho s^(i*2) := (pow_mul _ _ _).symm
      _=rho s^(2*i) := by congr 1;omega
      _=_ := pow_mul _ _ _
  rw [hp]

theorem delta_succ (s : ℝ) (i : ℕ) : delta s (i+1)=rho s*delta s i := by
  unfold delta
  rw [pow_succ]
  ring

theorem sequence_bounds {s : ℝ} (hs : 0<s) (hs1 : s<1) (i : ℕ) :
    0≤s^2*delta s i ∧ s^2*delta s i≤gamma s i ∧ gamma s i≤delta s i := by
  have hd := delta_pos hs hs1 i
  unfold gamma
  refine ⟨by positivity,?_,?_⟩
  · nlinarith [mul_nonneg hd.le (show 0≤s-s^2 by nlinarith)]
  · nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hs1.le)]

theorem sequence_recursion (s : ℝ) (i : ℕ) :
    gamma s (i+1)*delta s (i+1)=
      -(gamma s i-delta s i)*(gamma s i-s^2*delta s i) := by
  rw [gamma,delta_succ]
  unfold gamma rho
  ring

theorem sum_delta_sq {s : ℝ} (hs : 0<s) (hs1 : s<1) (n : ℕ) :
    ∑ i∈Finset.range n,delta s i^2=1-(rho s^2)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,delta_sq hs hs1,pow_succ]
    ring

theorem sum_delta_sq_le_one {s : ℝ} (hs : 0<s) (hs1 : s<1) (n : ℕ) :
    ∑ i∈Finset.range n,delta s i^2≤1 := by
  rw [sum_delta_sq hs hs1]
  exact sub_le_self _ (pow_nonneg (sq_nonneg _) _)

def ordinaryOffset (s : ℝ) (i : ℕ) : ℝ := s^2*rho s*(rho s^2)^i/(1-s^2)
def starOffset (s : ℝ) (N : ℕ) : ℝ := -s^2*(rho s^2)^(N+1)/(1-s^2)

theorem ordinary_offset_succ {s : ℝ} (hs : 0<s) (hs1 : s<1) (i : ℕ) :
    ordinaryOffset s i-ordinaryOffset s (i+1)=
      s*delta s (i+1)*(s*delta s i)/(1-s^2) := by
  rw [delta_succ]
  rw [show s*(rho s*delta s i)*(s*delta s i)=s^2*rho s*delta s i^2 by ring,
    delta_sq hs hs1]
  unfold ordinaryOffset
  rw [pow_succ]
  have hden : 1-s^2≠0 := by nlinarith
  field_simp
  ring

theorem offset_star_identity {s : ℝ} (hs : 0<s) (hs1 : s<1) (N i : ℕ) :
    (1-s^2)*(ordinaryOffset s i-starOffset s N)=
      s*delta s i^2-s^2*((rho s^2)^i-(rho s^2)^(N+1)) := by
  rw [delta_sq hs hs1]
  unfold ordinaryOffset starOffset rho
  have hden : 1-s^2≠0 := by nlinarith
  field_simp
  ring

end
end nesterov.Oracle.Geometric
