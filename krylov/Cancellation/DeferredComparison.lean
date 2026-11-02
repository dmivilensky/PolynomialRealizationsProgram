import krylov.Cancellation.DeferredSharp
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, original sharp deferred coefficient comparisons.
Use: prove calibration minimizes the true sharp matrix coefficient and every
nonamplifying damping improves FC, strictly at the printed nonterminal budgets.
Source: genuine positive CG energy tails, actual deferred Pythagorean norm
formula and finite nonnegative weighted sum comparison; no profile is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Variation
open scoped BigOperators
variable {n : ℕ}

/-- The squared genuine canonical CG error decreases along every real active prefix.
Use: all coefficient comparisons derive the nonnegative actual tail energy drop.
Article: main_krylov, thm:DC.
Proof: the true remaining-energy sums are nested and each actual step energy is nonnegative. -/
theorem canonical_error_sq_antitone (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i j : ℕ) (hij : i≤j) (hj : j≤referenceAtomCount base hb g) :
    ‖cgCanonicalError base g j‖^2≤‖cgCanonicalError base g i‖^2 := by
  rw [cgEnergy_tail base hb g hj,cgEnergy_tail base hb g (hij.trans hj)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    exact mem_Ico.mpr ⟨hij.trans (mem_Ico.mp hl).1,(mem_Ico.mp hl).2⟩
  · intro l _ _
    rw [cgEnergy_eq_norm_sq base hb]
    exact sq_nonneg _

/-- A genuine nonempty pre-final intermediate step tail has strictly positive
squared canonical error drop.
Use: strict FC improvement is proved from actual positive CG energy.
Article: main_krylov, thm:DC.
Proof: the true last intermediate energy is positive, and monotonicity bounds
the earlier actual error below by the preceding true error. -/
theorem canonical_intermediate_drop_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k l : ℕ) (hl : l+1<k)
    (hcount : k≤referenceAtomCount base hb g) :
    0<‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2 := by
  have hm := canonical_error_sq_antitone base hb g (l+1) (k-1) (by omega) (by omega)
  have hp := cgEnergy_pos base hb g (k-1) (by omega)
  rw [cgEnergy_drop base hb] at hp
  have he : k-1+1=k := by omega
  rw [he] at hp
  linarith

/-- Actual deferred tail norms increase monotonically with the absolute real
damping value on every true active reference.
Use: the real sharp matrix coefficient is minimized by calibration.
Article: main_krylov, thm:DC.
Proof: the genuine norm formula has a nonnegative actual intermediate energy
drop; compare squared damping values and true nonnegative vector norms. -/
theorem deferred_tail_norm_mono (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k l : ℕ) (hl : l<k)
    (hcount : k+1≤referenceAtomCount base hb g) (epsilon eta : ℝ) (habs : |epsilon| ≤ |eta|) :
    ‖deferredTail base g k epsilon l‖≤‖deferredTail base g k eta l‖ := by
  have hdrop := canonical_error_sq_antitone base hb g (l+1) k (by omega) (by omega)
  have hs : epsilon^2≤eta^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg epsilon) (abs_nonneg eta)).mpr habs
  have he := deferred_tail_norm_sq base hb g k l hl hcount epsilon
  have hf := deferred_tail_norm_sq base hb g k l hl hcount eta
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hdrop),
    norm_nonneg (deferredTail base g k epsilon l),norm_nonneg (deferredTail base g k eta l)]

/-- Actual deferred tail norms increase strictly with absolute damping when
there is a genuine intermediate CG step.
Use: identify the source's precise nonterminal-budget strictness condition.
Article: main_krylov, thm:DC.
Proof: true intermediate energy is strictly positive, so the genuine squared
norm formula has a strictly positive change in its squared damping term. -/
theorem deferred_tail_norm_strict (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k l : ℕ) (hl : l+1<k)
    (hcount : k+1≤referenceAtomCount base hb g) (epsilon eta : ℝ) (habs : |epsilon| < |eta|) :
    ‖deferredTail base g k epsilon l‖<‖deferredTail base g k eta l‖ := by
  have hdrop := canonical_intermediate_drop_pos base hb g k l hl (by omega)
  have hs : epsilon^2<eta^2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg epsilon) (abs_nonneg eta)).mpr habs
  have he := deferred_tail_norm_sq base hb g k l (by omega) hcount epsilon
  have hf := deferred_tail_norm_sq base hb g k l (by omega) hcount eta
  nlinarith [mul_pos (sub_pos.mpr hs) hdrop,
    norm_nonneg (deferredTail base g k epsilon l),norm_nonneg (deferredTail base g k eta l)]

/-- The calibrated original deferred sharp matrix coefficient is precisely
the sum of the original budgets times square-root last actual CG energy.
Use: this is the printed correction-free first-order minimax attaining value.
Article: main_krylov, thm:DC, W0 times norm(e_last).
Proof: at zero damping every genuine queried tail is exactly the actual last
CG step, whose true norm is the proved square root of its actual energy. -/
theorem deferred_calibrated_constant (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (omega : ℕ → ℝ) :
    (∑ l∈range k,omega l*‖deferredTail base g k 0 l‖)=
      (∑ l∈range k,omega l)*Real.sqrt (cgEnergy base g k) := by
  simp only [deferredTail,zero_smul,zero_add]
  rw [cgEnergy_sqrt base hb,Finset.sum_mul]

/-- Nonamplifying original damping never exceeds FC's true sharp coefficient,
and the comparison is strict at exactly the printed positive intermediate budgets.
Use: the original arithmetic Gauss--Radau bound supplies a damping norm below one.
Article: main_krylov, thm:DC, strict sharp FC coefficient improvement.
Proof: actual tail norm monotonicity bounds every genuine weighted term;
positive intermediate energy makes one original positive-budget term strict. -/
theorem deferred_coefficient_le_FC (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (epsilon : ℝ) (habs : |epsilon|≤1) (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    (∑ l∈range k,omega l*‖deferredTail base g k epsilon l‖)≤
      ∑ l∈range k,omega l*‖deferredTail base g k 1 l‖ := by
  apply sum_le_sum
  intro l hl
  exact mul_le_mul_of_nonneg_left
    (deferred_tail_norm_mono base hb g k l (mem_range.mp hl) hcount epsilon 1 (by simpa only [abs_one] using habs))
    (homega l (mem_range.mp hl))

/-- A genuine positive intermediate budget gives strict sharp improvement
over FC for every original damping value with norm strictly below one.
Use: zero budgets, the final-only budget and two-dimensional equality are retained.
Article: main_krylov, thm:DC, exact strictness condition.
Proof: all true terms are nonincreasing, and a positive original intermediate
budget multiplies one strictly smaller actual deferred-tail norm. -/
theorem deferred_coefficient_strict_FC (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (epsilon : ℝ) (habs : |epsilon|<1) (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l)
    (hpositive : ∃ l,l+1<k ∧ 0<omega l) :
    (∑ l∈range k,omega l*‖deferredTail base g k epsilon l‖)<
      ∑ l∈range k,omega l*‖deferredTail base g k 1 l‖ := by
  apply sum_lt_sum
  · intro l hl
    exact mul_le_mul_of_nonneg_left
      (deferred_tail_norm_mono base hb g k l (mem_range.mp hl) hcount epsilon 1 (by simpa only [abs_one] using habs.le))
      (homega l (mem_range.mp hl))
  · obtain ⟨l,hl,hw⟩ := hpositive
    refine ⟨l,mem_range.mpr (by omega),?_⟩
    exact mul_lt_mul_of_pos_left
      (deferred_tail_norm_strict base hb g k l hl hcount epsilon 1 (by simpa only [abs_one] using habs)) hw

end
end krylov.Cancellation
