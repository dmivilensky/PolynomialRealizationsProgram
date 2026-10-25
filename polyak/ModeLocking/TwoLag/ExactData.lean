import polyak.ModeLocking.TwoLag.Extension
import polyak.ModeLocking.TwoLag.Algebra
import polyak.ModeLocking.Analysis.Perturbation

/-! The primary E1–E4 hypotheses of Theorem exact, before any regularity
conclusion is constructed. E3 uses its canonical positive kernel weights. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Matrix Set

structure ExactData (q : Tuning) (s : ℝ) (K L : ℕ) where
  K_ge : 2≤K
  L_ge : K+2≤L
  u : Fin 2→Frequency
  interior : ∀i,0<(u i : ℝ) ∧ (u i : ℝ)<Real.pi
  a : ℝ
  b : ℝ
  a_pos : 0<a
  b_pos : 0<b
  normalized : a+b=1
  nonpos : ∀x∈Icc 0 Real.pi,extension q s K a b x≤0
  zero_set : ∀x∈Ioo 0 Real.pi,extension q s K a b x=0 ↔ x=(u 0 : ℝ) ∨ x=(u 1 : ℝ)
  endpoint_curv : deriv^[2] (extension q s K a b) 0<0
  curv : ∀i,deriv^[2] (extension q s K a b) (u i : ℝ)<0
  sign₁ : 0<(Geometry.shiftedCurve q s).lag 1 (u 0)
  sign₂ : (Geometry.shiftedCurve q s).lag 1 (u 1)<0
  opposite₁ : (Geometry.shiftedCurve q s).lag (-(K : ℤ)) (u 0)<0
  opposite₂ : 0<(Geometry.shiftedCurve q s).lag (-(K : ℤ)) (u 1)
  grid : ∀i,u i∈periodicGrid L
  inactive : ∀ r : ℤ, 0 < r → r < (L : ℤ) → r ≠ 1 → r ≠ (L : ℤ)-K →
    -(Geometry.shiftedCurve q s).lag 1 (u 1)*(Geometry.shiftedCurve q s).lag r (u 0)+
      (Geometry.shiftedCurve q s).lag 1 (u 0)*(Geometry.shiftedCurve q s).lag r (u 1)>0
  minimizer : -(Geometry.shiftedCurve q s).lag 1 (u 1)*(Geometry.shiftedCurve q s).minimizer (u 0)+
    (Geometry.shiftedCurve q s).lag 1 (u 0)*(Geometry.shiftedCurve q s).minimizer (u 1)>0
  determinant : Matrix.det (fun i r : Fin 2=>Real.sin
    (((![1,-(K : ℤ)] : Fin 2→ℤ) r : ℝ)*(u i : ℝ)-Geometry.shiftedCurve q s (u i)))≠0

namespace ExactData
variable {q : Tuning} {s : ℝ} {K L : ℕ} (D : ExactData q s K L)

def A : ℝ := (Geometry.shiftedCurve q s).lag 1 (D.u 0)
def B : ℝ := (Geometry.shiftedCurve q s).lag 1 (D.u 1)

def primal (i : Fin 2) : NNReal := ⟨(if i=0 then -D.B else D.A)/(D.A-D.B), by
  have hA : 0<D.A := D.sign₁
  have hB : D.B<0 := D.sign₂
  have hd : 0<D.A-D.B := by linarith
  split_ifs
  · exact div_nonneg (by linarith) hd.le
  · exact div_nonneg hA.le hd.le⟩

def reps (_D : ExactData q s K L) : Fin 2→ℤ := ![1,(L : ℤ)-K]

theorem u_injective : Function.Injective D.u := by
  intro i j hij
  by_contra hne
  have h0 := D.sign₁
  have h1 := D.sign₂
  fin_cases i <;> fin_cases j <;> first | exact False.elim (hne rfl) | (simp_all; linarith)

theorem primal_pos (i : Fin 2) : 0<D.primal i := by
  have hA : 0<D.A := D.sign₁
  have hB : D.B<0 := D.sign₂
  change (0 : ℝ)<(if i=0 then -D.B else D.A)/(D.A-D.B)
  have hd : 0<D.A-D.B := by linarith
  split_ifs
  · exact div_pos (by linarith) hd
  · exact div_pos hA hd

theorem primal_sum : ∑i,D.primal i=1 := by
  rw [Fin.sum_univ_two]
  apply NNReal.coe_injective
  change (-D.B)/(D.A-D.B)+D.A/(D.A-D.B)=1
  have hd : D.A-D.B≠0 := by have hA:=D.sign₁;have hB:=D.sign₂;dsimp [A,B];linarith
  field_simp
  ring

theorem extension_zero (i : Fin 2) : extension q s K D.a D.b (D.u i : ℝ)=0 :=
  (D.zero_set _ (D.interior i)).mpr (by fin_cases i <;> simp)

theorem dual_zero (i : Fin 2) :
    D.a*(Geometry.shiftedCurve q s).lag 1 (D.u i)+
      D.b*(Geometry.shiftedCurve q s).lag (-(K : ℤ)) (D.u i)=0 := by
  simpa only [extension_actual] using D.extension_zero i

theorem lag_reps (i j : Fin 2) :
    (Geometry.shiftedCurve q s).lag (D.reps i) (D.u j)=
      (Geometry.shiftedCurve q s).lag ((![1,-(K : ℤ)] : Fin 2→ℤ) i) (D.u j) := by
  fin_cases i
  · rfl
  · change (Geometry.shiftedCurve q s).lag ((L : ℤ)-K) (D.u j)=
      (Geometry.shiftedCurve q s).lag (-(K : ℤ)) (D.u j)
    have h := lag_add_mul_grid (Geometry.shiftedCurve q s) (D.grid j) (-(K : ℤ)) 1
    convert h using 1
    congr 1
    ring

end ExactData
end polyak.ModeLocking.TwoLag
