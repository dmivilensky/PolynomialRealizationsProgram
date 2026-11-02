import krylov.Tensor.ReferenceAmplification
import krylov.Tensor.SineWitness

/-!
Article: main_krylov, thm:Hp, the compatible harmonic lower bound.
Use: construct an admissible actual tensor whose true reference response
has the printed oldest-direction component. All directions and tails come
from the executed quadratic CG reference, rather than prescribed coefficients.
Source: the harmonic witness in the article and exact CG orthogonality.
-/

/-!
Article: krylov, Proposition E.8 [thm:Hp].

The computed CG frame has an attained symmetric cubic spectral/nuclear dual coefficient, a
genuine lower witness and the printed independent-operator upper bounds.
The tensor-product norm in the formal dual is the proved projective/nuclear norm; the lower
energy factor uses the true canonical CG step length √c0.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Reference krylov.Variation krylov.LinearAlgebra Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator TensorProduct NNReal
variable {n : ℕ}

/-- An actual normalized canonical CG step extracts its own true step length and annihilates every other active step.
Article: main_krylov, thm:Hp.
Proof: true zero-safe normalization and the derived actual orthonormal frame. -/
theorem canonical_step_unit_pair (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i j : Fin (referenceAtomCount A hA g)) :
    inner ℝ (canonicalCGUnitStep A g i.val) (canonicalCGStep A g j.val) =
      if i = j then ‖canonicalCGStep A g j.val‖ else 0 := by
  have hs : canonicalCGStep A g j.val =
      ‖canonicalCGStep A g j.val‖ • canonicalCGUnitStep A g j.val :=
    (NormedSpace.norm_smul_normalize _).symm
  conv_lhs => rw [hs]
  rw [inner_smul_right, orthonormal_iff_ite.mp (canonicalCG_frame A hA g) i j]
  split_ifs <;> simp only [mul_one, mul_zero]

/-- The actual oldest response component is the sum of the actual oldest cubic contractions.
Article: main_krylov, thm:Hp.
Proof: actual orthonormality removes every other coordinate of each true old flag. -/
theorem inner_referenceCubicResponse_first (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0 < referenceAtomCount A hA g)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ) :
    inner ℝ (canonicalCGUnitStep A g 0) (referenceCubicResponse A hA g f) =
      ∑ l : Fin (referenceAtomCount A hA g - 1),
        f ![canonicalCGUnitStep A g 0, referenceMidpointDrift A g l.val, remainingTail A g l.val] := by
  let i₀ : Fin (referenceAtomCount A hA g) := ⟨0, hN⟩
  have horth (i : Fin (referenceAtomCount A hA g)) :
      inner ℝ (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g i.val) =
        if i₀ = i then 1 else 0 := orthonormal_iff_ite.mp (canonicalCG_frame A hA g) i₀ i
  unfold referenceCubicResponse flagResponse
  simp only [inner_sum, inner_smul_right, horth, mul_ite, mul_one, mul_zero]
  apply sum_congr rfl
  intro l _
  simp [referenceFlagIndices, i₀]

/-- The true oldest coordinate of every actual midpoint drift is confined to its first increment.
Article: main_krylov, thm:Hp.
Proof: each genuine midpoint difference is half two actual orthogonal CG steps. -/
theorem reference_midpoint_first_coordinate (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0 < referenceAtomCount A hA g)
    (l : Fin (referenceAtomCount A hA g - 1)) :
    inner ℝ (canonicalCGUnitStep A g 0) (referenceMidpointDrift A g l.val) =
      if l.val = 0 then ‖canonicalCGStep A g 0‖ / 2 else 0 := by
  have hl : l.val+1 < referenceAtomCount A hA g := by omega
  have h₀ := canonical_step_unit_pair A hA g ⟨0, hN⟩ ⟨l.val, by omega⟩
  have h₁ := canonical_step_unit_pair A hA g ⟨0, hN⟩ ⟨l.val+1, hl⟩
  simp only [Fin.mk.injEq] at h₀ h₁
  rw [referenceMidpointDrift, inner_smul_right, inner_add_right, h₀, h₁,
    ite_eq_right (by omega : ¬0 = l.val+1), add_zero]
  by_cases hz : l.val = 0
  · rw [hz, ite_eq_left rfl, ite_eq_left rfl]
    ring
  · rw [ite_eq_right (Ne.symm hz), ite_eq_right hz, mul_zero]

/-- An actual admissible harmonic tensor attains the printed oldest response component.
Article: main_krylov, thm:Hp, lower-bound witness.
Proof: the true remaining tail is orthogonal to the oldest computed step;
only the first actual midpoint drift has a nonzero oldest coordinate. -/
theorem reference_cubic_lower_witness (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2 ≤ referenceAtomCount A hA g) :
    ∃ f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ,
      IsSymmetricForm f ∧ (∀ x, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ 2) ∧
      ‖canonicalCGStep A g 0‖ * ‖cgCanonicalError A g 1‖ ≤ ‖referenceCubicResponse A hA g f‖ := by
  let e := canonicalCGUnitStep A g 0
  let v := remainingTail A g 0
  let h := NormedSpace.normalize v
  have he : ‖e‖ = 1 := (firstStep_common A hA g (by omega)).1
  have hv : v ≠ 0 := remainingTail_ne_zero A hA g 0 (by omega)
  have hh : ‖h‖ = 1 := NormedSpace.norm_normalize hv
  have htail (l : ℕ) (hl : l < referenceAtomCount A hA g) :
      inner ℝ e (remainingTail A g l) = 0 :=
    ((oldFlag A g l).mem_orthogonal _).mp (remainingTail_orthogonal A hA g l hl)
      e (unitStep_mem_oldFlag A g (Nat.zero_le l))
  have heh : inner ℝ e h = 0 := by
    rw [show h = ‖v‖⁻¹ • v from rfl, inner_smul_right]
    change ‖v‖⁻¹ * inner ℝ e (remainingTail A g 0) = 0
    rw [htail 0 (by omega), mul_zero]
  have hhe : inner ℝ h e = 0 := (real_inner_comm e h).trans heh
  have hhv : inner ℝ h v = ‖v‖ := by
    rw [real_inner_comm]
    exact inner_normalize v
  let T := sineCubic (innerSL ℝ e) (innerSL ℝ h)
  let f := cubicUncurried T
  refine ⟨f, cubicUncurried_symmetric T,
    cubicUncurried_diagonal_bound T (sineCubic_diagonal_bound e h he hh heh), ?_⟩
  have hc : inner ℝ e (referenceCubicResponse A hA g f) =
      ‖canonicalCGStep A g 0‖ * ‖v‖ := by
    rw [inner_referenceCubicResponse_first A hA g (by omega)]
    let j₀ : Fin (referenceAtomCount A hA g - 1) := ⟨0, by omega⟩
    have hs (l : Fin (referenceAtomCount A hA g - 1)) :
        f ![e, referenceMidpointDrift A g l.val, remainingTail A g l.val] =
          if l = j₀ then ‖canonicalCGStep A g 0‖ * ‖v‖ else 0 := by
      change T.form e (referenceMidpointDrift A g l.val) (remainingTail A g l.val) = _
      rw [sineCubic_first_slice e h he hhe, reference_midpoint_first_coordinate A hA g (by omega) l,
        htail l.val (by omega), mul_zero, add_zero]
      by_cases hl : l = j₀
      · subst l
        change 2 * ((if (0 : ℕ) = 0 then ‖canonicalCGStep A g 0‖ / 2 else 0) * inner ℝ h v) = _
        rw [ite_eq_left rfl, ite_eq_left rfl, hhv]
        ring
      · have hlv : l.val ≠ 0 := by intro hz; exact hl (Fin.ext hz)
        rw [ite_eq_right hlv, ite_eq_right hl, zero_mul, mul_zero]
    change (∑ l : Fin (referenceAtomCount A hA g - 1),
      f ![e, referenceMidpointDrift A g l.val, remainingTail A g l.val]) = _
    simp_rw [hs]
    simp
  have hb := real_inner_le_norm e (referenceCubicResponse A hA g f)
  rw [he, one_mul, hc, remainingTail_norm] at hb
  exact hb

/-- The actual compatible coefficient has all printed sharp-profile bounds and its exact attained nuclear formula.
Article: main_krylov, thm:Hp, complete proposition.
Proof: combine the genuine attained reference duality with the explicit
admissible harmonic tensor and the genuine CG energy-profile estimate. -/
theorem reference_cubic_amplification_bounds [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hN : 2 ≤ referenceAtomCount A hA g) :
    ∃ Γ : ℝ≥0,
      IsGreatest ((fun u : EuclideanSpace ℝ (Fin n) =>
        2 * ‖tensorSymmetrization (referenceCubicTarget A hA g u)‖₊) '' {u | ‖u‖ = 1}) Γ ∧
      IsGreatest ((fun f : ContinuousMultilinearMap ℝ
          (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ => ‖referenceCubicResponse A hA g f‖) ''
        {f | IsSymmetricForm f ∧ ∀ x, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ 2}) (Γ : ℝ) ∧
      ‖canonicalCGStep A g 0‖ * ‖cgCanonicalError A g 1‖ ≤ (Γ : ℝ) ∧
      (Γ : ℝ) ≤ referenceOperatorCoefficient A g (referenceAtomCount A hA g) ∧
      referenceOperatorCoefficient A g (referenceAtomCount A hA g) ≤
        ‖cgCanonicalError A g 0‖ * ‖cgCanonicalError A g 1‖ +
          (referenceAtomCount A hA g - 2 : ℕ) * ‖cgCanonicalError A g 1‖ ^ 2 := by
  obtain ⟨Γ, hΓ, hresp, hupper, hprofile⟩ := reference_cubic_amplification A hA g hN
  obtain ⟨f, hf, hd, hlower⟩ := reference_cubic_lower_witness A hA g hN
  exact ⟨Γ, hΓ, hresp, hlower.trans (hresp.2 ⟨f, ⟨hf, hd⟩, rfl⟩), hupper, hprofile⟩

end
end krylov.Tensor
