import nesterov.Oracle.GeometricScalars
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Concrete finite geometric data for the DT22 extension. Heights differ
from Appendix A by one common additive constant. -/
namespace nesterov.Oracle.Geometric
noncomputable section
open Finset Set
open scoped BigOperators RealInnerProductSpace

abbrev ChainSpace (N : ℕ) := EuclideanSpace ℝ (Fin (N+1))

def slope (N : ℕ) (s : ℝ) (j : ℕ) : ChainSpace N :=
  WithLp.toLp 2 (fun ℓ=>if ℓ.val<j then s^2*delta s ℓ.val else
    if ℓ.val=j then s*delta s ℓ.val else 0)

def offset (N : ℕ) (s : ℝ) (j : ℕ) : ℝ :=
  if j<N+1 then ordinaryOffset s j else starOffset s N

def starPoint (N : ℕ) (s : ℝ) : ChainSpace N := WithLp.toLp 2 (fun ℓ=> -delta s ℓ.val)

theorem slope_apply (N : ℕ) (s : ℝ) (j : ℕ) (ℓ : Fin (N+1)) :
    slope N s j ℓ=if ℓ.val<j then s^2*delta s ℓ.val else
      if ℓ.val=j then s*delta s ℓ.val else 0 := rfl

theorem starPoint_apply (N : ℕ) (s : ℝ) (ℓ : Fin (N+1)) :
    starPoint N s ℓ= -delta s ℓ.val := rfl

theorem slope_bounds {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (j : ℕ) (ℓ : Fin (N+1)) :
    0≤slope N s j ℓ ∧ slope N s j ℓ≤s*delta s ℓ.val := by
  rw [slope_apply]
  have hd := delta_pos hs hs1 ℓ.val
  have hsd := sequence_bounds hs hs1 ℓ.val
  split_ifs
  · exact ⟨hsd.1,hsd.2.1⟩
  · exact ⟨mul_nonneg hs.le hd.le,le_rfl⟩
  · exact ⟨le_rfl,mul_nonneg hs.le hd.le⟩

theorem slope_after {N : ℕ} (s : ℝ) {j : ℕ} {ℓ : Fin (N+1)} (h : j<ℓ.val) :
    slope N s j ℓ=0 := by
  simp only [slope_apply,not_lt.mpr h.le,ite_false,ne_of_gt h]

theorem slope_before {N : ℕ} (s : ℝ) {j : ℕ} {ℓ : Fin (N+1)} (h : ℓ.val<j) :
    slope N s j ℓ=s^2*delta s ℓ.val := by rw [slope_apply,ite_eq_left h]

theorem slope_self {N : ℕ} (s : ℝ) (j : Fin (N+1)) :
    slope N s j.val j=s*delta s j.val := by simp only [slope_apply,lt_self_iff_false,ite_false,ite_true]

theorem slope_star (N : ℕ) (s : ℝ) (ℓ : Fin (N+1)) :
    slope N s (N+1) ℓ=s^2*delta s ℓ.val := slope_before s ℓ.isLt

theorem slope_tail_constant {N : ℕ} (s : ℝ) {j : ℕ} (hj : N+1≤j) :
    slope N s j=slope N s (N+1) := by
  ext ℓ
  rw [slope_before s (lt_of_lt_of_le ℓ.isLt hj),slope_star]

theorem star_stationary (N : ℕ) (s : ℝ) :
    s^2 • starPoint N s+slope N s (N+1)=0 := by
  ext ℓ
  simp only [PiLp.add_apply,PiLp.smul_apply,starPoint_apply,slope_star,smul_eq_mul,PiLp.zero_apply]
  ring

theorem starPoint_norm_le {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    ‖starPoint N s‖≤1 := by
  have hnorm : ‖starPoint N s‖^2=∑ ℓ : Fin (N+1),delta s ℓ.val^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [starPoint_apply,neg_sq]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ=>delta s i^2) (N+1)] at hnorm
  have hb := sum_delta_sq_le_one hs hs1 (N+1)
  nlinarith [norm_nonneg (starPoint N s)]

end
end nesterov.Oracle.Geometric
