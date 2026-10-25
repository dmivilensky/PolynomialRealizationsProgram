import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Appendix E: the exact cutoff above the larger root in the sampling lemma. -/
noncomputable section
namespace polyak.Global.Sampling

def cutoffPolynomial (A B C x : ℝ) : ℝ:=A*x^2-B*x-C

def largerRoot (A B C : ℝ) : ℝ:=(B+Real.sqrt (B^2+4*A*C))/(2*A)

def lagCutoff (A B C : ℝ) : ℕ:=Nat.floor (largerRoot A B C)+1

theorem largerRoot_nonneg {A B C : ℝ} (hA : 0<A) (hB : 0≤B) :
    0≤largerRoot A B C := by unfold largerRoot; positivity

theorem largerRoot_zero {A B C : ℝ} (hA : 0<A) (hC : 0≤C) :
    cutoffPolynomial A B C (largerRoot A B C)=0 := by
  have hd : 0≤B^2+4*A*C:=by positivity
  have hs:=Real.sq_sqrt hd
  unfold cutoffPolynomial largerRoot
  generalize Real.sqrt (B^2+4*A*C)=d at hs ⊢
  field_simp
  nlinarith

theorem twice_largerRoot_ge {A B C : ℝ} (hA : 0<A) :
    B≤2*A*largerRoot A B C := by
  unfold largerRoot
  have he : 2*A*((B+Real.sqrt (B^2+4*A*C))/(2*A))=B+Real.sqrt (B^2+4*A*C):=by field_simp
  rw [he]
  linarith [Real.sqrt_nonneg (B^2+4*A*C)]

theorem cutoffPolynomial_pos_above_root {A B C x : ℝ} (hA : 0<A) (hC : 0≤C)
    (hx : largerRoot A B C<x) : 0<cutoffPolynomial A B C x := by
  have hz:=largerRoot_zero (B:=B) hA hC
  have hm:=twice_largerRoot_ge (B:=B) (C:=C) hA
  have hp : 0<A*(x-largerRoot A B C)^2:=mul_pos hA (sq_pos_of_pos (sub_pos.mpr hx))
  have hn : 0≤(2*A*largerRoot A B C-B)*(x-largerRoot A B C):=mul_nonneg (by linarith) (by linarith)
  dsimp [cutoffPolynomial] at hz ⊢
  nlinarith

theorem lagCutoff_properties {A B C : ℝ} (hA : 0<A) (hC : 0≤C) :
    1≤lagCutoff A B C ∧ largerRoot A B C<(lagCutoff A B C:ℝ) ∧
      0<cutoffPolynomial A B C (lagCutoff A B C) ∧
      ∀x : ℝ,(lagCutoff A B C:ℝ)≤x→
        cutoffPolynomial A B C (lagCutoff A B C)≤cutoffPolynomial A B C x := by
  have hr : largerRoot A B C<(lagCutoff A B C:ℝ):=by
    simpa only [lagCutoff,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (largerRoot A B C)
  refine ⟨by unfold lagCutoff; omega,hr,cutoffPolynomial_pos_above_root hA hC hr,?_⟩
  intro x hx
  have hm:=twice_largerRoot_ge (B:=B) (C:=C) hA
  have hcoef : 0≤2*A*(lagCutoff A B C:ℝ)-B:=by nlinarith
  have hp : 0≤A*(x-lagCutoff A B C)^2:=mul_nonneg hA.le (sq_nonneg _)
  have hn : 0≤(2*A*(lagCutoff A B C:ℝ)-B)*(x-lagCutoff A B C):=mul_nonneg hcoef (sub_nonneg.mpr hx)
  dsimp [cutoffPolynomial]
  nlinarith

end polyak.Global.Sampling
