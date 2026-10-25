import polyak.Boundary.P5.CriticalAlgebra
import polyak.Boundary.P5.RealChebyshev
import polyak.Spiral.KernelPolynomial
import polyak.Boundary.Tail

/-!
Article: Proposition p5divslack, exact critical first-order slack values.
Use: every nonactive critical first-order slack is positive, for all lags.
Proof: the four active zeros are the four critical primal equations; the
sharp one-atom tail bound gives Yₘ≥−1/2 and handles every m≥6 at once.
-/

noncomputable section
namespace polyak.Boundary.P5
open Spectral

/-- Article: the auxiliary atom contribution Yₘˢ in the first-order slack. -/
def criticalY (m : ℕ) (σ y : ℝ) : ℝ :=
  (3/4-y^2)*(1-chebT m y)+σ*(1-y^2)*chebU (m-1) y

/-- Article: the three residue-class formulas of Proposition p5divslack. -/
def firstSlack (m : ℕ) (σ : ℝ) : ℝ :=
  if m%3=0 then (m : ℝ)^2/2-σ*m*(B₀+D₀)+P₀*criticalY m σ y₀
  else (m : ℝ)^2/2+(B₀-3*A₀)+σ*m*B₀-σ*m*D₀+P₀*criticalY m σ y₀

/-- Article: signs and residue classes whose three-cycle slack vanishes. -/
def CriticalPair (m : ℕ) (σ : ℝ) : Prop :=
  (σ= -1 ∨ σ=1) ∧ (m%3=0 ∨ (m%3=1 ∧ σ= -1) ∨ (m%3=2 ∧ σ=1))

/-- Article: the four active primal constraints of P₅. -/
def ActivePair (m : ℕ) (σ : ℝ) : Prop :=
  (m=1 ∧ σ= -1) ∨ (m=2 ∧ σ=1) ∨ (m=3 ∧ σ=1) ∨ (m=5 ∧ σ=1)

/-- Article: the auxiliary contribution has a uniform lower bound, stronger
than the absolute bound used in the source proof. -/
theorem criticalY_lower (m : ℕ) (hm : 1 ≤ m) (σ : ℝ) (hσ : σ= -1 ∨ σ=1) :
    -(1/2 : ℝ) ≤ criticalY m σ y₀ := by
  let c : Frequency := ⟨y₀,⟨y₀_interior.1.le,y₀_interior.2.le⟩⟩
  rcases hσ with rfl | rfl
  · have h := pointwise_lag_tail (1/2) 0 m hm c 1 (Or.inl rfl)
    norm_num [lagA,lagD,lagB,g,c] at h
    dsimp [criticalY]
    nlinarith
  · have h := pointwise_lag_tail (1/2) 0 m hm c (-1) (Or.inr rfl)
    norm_num [lagA,lagD,lagB,g,c] at h
    dsimp [criticalY]
    nlinarith

/-- Article: all large first-order slacks are strictly positive, uniformly in sign.
Use: this proves all m≥8 from the source and also covers m=6,7. -/
theorem firstSlack_positive_large {m : ℕ} (hm : 6 ≤ m) {σ : ℝ}
    (hσ : σ= -1 ∨ σ=1) : 0 < firstSlack m σ := by
  have hy := criticalY_lower m (by omega) σ hσ
  have hpy : -(129/100 : ℝ) < P₀*criticalY m σ y₀ := by
    have hp := mul_le_mul_of_nonneg_left hy P₀_bounds.1.le
    nlinarith [P₀_bounds.2]
  have hmR : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpoly : 0 < (m : ℝ)^2/2-(237/100 : ℝ)*m-181/100-129/100 := by
    nlinarith [sq_nonneg ((m : ℝ)-6)]
  have hBD : -(237/100 : ℝ) < B₀+D₀ ∧ B₀+D₀ < 237/100 := by
    have hB := B₀_fine_bounds
    have hD := D₀_fine_bounds
    constructor <;> linarith
  have hBD' : -(237/100 : ℝ) < B₀-D₀ ∧ B₀-D₀ < 237/100 := by
    have hB := B₀_fine_bounds
    have hD := D₀_fine_bounds
    constructor <;> linarith
  have hBA : -(181/100 : ℝ) < B₀-3*A₀ := by
    have hB := B₀_fine_bounds
    have hA := A₀_fine_bounds
    linarith
  have h₁ := mul_nonneg hm0 (show 0 ≤ B₀+D₀+237/100 by linarith [hBD.1])
  have h₂ := mul_nonneg hm0 (show 0 ≤ 237/100-(B₀+D₀) by linarith [hBD.2])
  have h₃ := mul_nonneg hm0 (show 0 ≤ B₀-D₀+237/100 by linarith [hBD'.1])
  have h₄ := mul_nonneg hm0 (show 0 ≤ 237/100-(B₀-D₀) by linarith [hBD'.2])
  unfold firstSlack
  split_ifs
  · rcases hσ with rfl | rfl <;> nlinarith
  · rcases hσ with rfl | rfl <;> nlinarith

/-- Article: the four active first-order slacks vanish exactly. -/
theorem active_firstSlacks_zero :
    firstSlack 1 (-1)=0 ∧ firstSlack 2 1=0 ∧ firstSlack 3 1=0 ∧ firstSlack 5 1=0 := by
  have h := critical_primal_equations
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [firstSlack,criticalY,chebT,chebU]
    nlinarith [h.1]
  · norm_num [firstSlack,criticalY,chebT,chebU,Polynomial.Chebyshev.T_two]
    nlinarith [h.2.1]
  · norm_num [firstSlack,criticalY,chebU,Polynomial.Chebyshev.U_two]
    nlinarith [h.2.2.1]
  · norm_num [firstSlack,criticalY]
    nlinarith [h.2.2.2]

/-- Article: the two remaining small critical first-order slacks are strictly positive. -/
theorem small_firstSlacks_positive : 0 < firstSlack 3 (-1) ∧ 0 < firstSlack 4 (-1) := by
  have h3 := mul_le_mul_of_nonneg_left (criticalY_lower 3 (by omega) (-1) (Or.inl rfl)) P₀_bounds.1.le
  have h4 := mul_le_mul_of_nonneg_left (criticalY_lower 4 (by omega) (-1) (Or.inl rfl)) P₀_bounds.1.le
  have hA := A₀_bounds
  have hB := B₀_fine_bounds
  have hD := D₀_fine_bounds
  have hP := P₀_bounds
  norm_num [firstSlack]
  constructor <;> nlinarith

/-- Article: first-order positivity at every nonactive critical pair, without a finite-lag cutoff. -/
theorem firstSlack_positive_of_not_active {m : ℕ} {σ : ℝ} (hm : 1 ≤ m)
    (hc : CriticalPair m σ) (ha : ¬ActivePair m σ) : 0 < firstSlack m σ := by
  by_cases hm6 : 6 ≤ m
  · exact firstSlack_positive_large hm6 hc.1
  · have hm5 : m ≤ 5 := by omega
    rcases hc.1 with rfl | rfl
    · interval_cases m <;> norm_num [CriticalPair,ActivePair] at *
      · exact small_firstSlacks_positive.1
      · exact small_firstSlacks_positive.2
    · interval_cases m <;> norm_num [CriticalPair,ActivePair] at *

/-- Article: first-order critical zeros are precisely the four active pairs. -/
theorem firstSlack_eq_zero_iff {m : ℕ} {σ : ℝ} (hm : 1 ≤ m) (hc : CriticalPair m σ) :
    firstSlack m σ=0 ↔ ActivePair m σ := by
  constructor
  · intro hz
    by_contra ha
    have hp := firstSlack_positive_of_not_active hm hc ha
    rw [hz] at hp
    exact (lt_irrefl _ hp).elim
  · intro ha
    rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact active_firstSlacks_zero.1
    · exact active_firstSlacks_zero.2.1
    · exact active_firstSlacks_zero.2.2.1
    · exact active_firstSlacks_zero.2.2.2

end polyak.Boundary.P5
