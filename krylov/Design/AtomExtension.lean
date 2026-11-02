import krylov.Design.SupportExclusion
import Mathlib.SetTheory.Cardinal.Embedding

/-!
Article: main_krylov, apC:lem:natoms, the actual atom-padding approximation.
Use: extend any finite physical probability design to exactly N distinct atoms
without decreasing its mixed objective by more than any prescribed tolerance.
Source: the elementary small-positive-mass perturbation in the article;
mathlib supplies extension of finite embeddings into the infinite interval.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory jacobi.Finite
open scoped BigOperators InnerProductSpace NNReal

/-- Finite probability data give their actual weighted square integral.
Article: main_krylov, apC:lem:natoms.
Proof: reuse the genuine atomic-integral and finite spectral inner-product dictionaries. -/
theorem polynomialEnergy_atomic_sum {N : ℕ} (I : chebyshev1.SpectralInterval)
    (M : DiscreteMeasure N) (hM : ∀ i, M.node i ∈ Set.Icc I.mu I.L) (p : ℝ[X]) :
    polynomialEnergy (spectralCoordinate I)
      (atomicProbability M (fun i => ⟨M.node i, hM i⟩ : Fin N → Spectrum I)) p =
      ∑ i, M.weight i * (p.eval (M.node i)) ^ 2 := by
  rw [polynomialEnergy_atomic _ _ _ (fun _ => rfl),
    ← real_inner_self_eq_norm_sq, DiscreteMeasure.inner_evaluate]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Extend the actual old spectral points to an arbitrary larger number of distinct interval points.
Article: main_krylov, apC:lem:natoms.
Proof: the physical interval is infinite, so mathlib extends its finite embedding. -/
theorem exists_spectral_embedding_extension {K R : ℕ} (I : chebyshev1.SpectralInterval)
    (M : DiscreteMeasure K) (hM : ∀ i, M.node i ∈ Set.Icc I.mu I.L) :
    ∃ z : Fin (K + R) ↪ Spectrum I,
      ∀ i : Fin K, z (Fin.castAdd R i) = ⟨M.node i, hM i⟩ := by
  let old : Fin K ↪ Spectrum I :=
    ⟨fun i => ⟨M.node i, hM i⟩, fun _ _ h => M.distinct (congrArg Subtype.val h)⟩
  have : Infinite (Spectrum I) := Set.Icc.infinite I.mu_lt_L
  obtain ⟨z, hz⟩ := Fin.Embedding.restrictSurjective_of_add_le_ENatCard
    (α := Spectrum I) (m := K) (n := R) (by simp) old
  exact ⟨z, fun i => congrArg (fun e : Fin K ↪ Spectrum I => e i) hz⟩

/-- A positive-mass extension with exactly K+R distinct atoms and the original first K nodes.
Article: main_krylov, apC:lem:natoms. -/
def extendedMeasure {K R : ℕ} (I : chebyshev1.SpectralInterval) (M : DiscreteMeasure K)
    (z : Fin (K + R) ↪ Spectrum I) (hR : 0 < R) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    DiscreteMeasure (K + R) where
  node i := (z i).val
  distinct _ _ hij := z.injective (Subtype.ext hij)
  weight := Fin.append (fun i => (1 - s) * M.weight i) (fun _ => s / R)
  positive := Fin.addCases
    (fun i => by simp only [Fin.append_left]; exact mul_pos (by linarith) (M.positive i))
    (fun _ => by simp only [Fin.append_right]; exact div_pos hs (by exact_mod_cast hR))
  probability := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, ← Finset.mul_sum, M.probability,
      mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hRn : (R : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
    field_simp
    ring

/-- The extension retains the original energy with coefficient 1-s and adds a nonnegative energy.
Article: main_krylov, apC:lem:natoms.
Proof: split the true finite square integral into the old and the newly added atoms. -/
theorem polynomialEnergy_extended_lower {K R : ℕ} (I : chebyshev1.SpectralInterval)
    (M : DiscreteMeasure K) (hM : ∀ i, M.node i ∈ Set.Icc I.mu I.L)
    (z : Fin (K + R) ↪ Spectrum I)
    (hz : ∀ i : Fin K, z (Fin.castAdd R i) = ⟨M.node i, hM i⟩)
    (hR : 0 < R) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) (p : ℝ[X]) :
    (1 - s) * polynomialEnergy (spectralCoordinate I)
      (atomicProbability M (fun i => ⟨M.node i, hM i⟩ : Fin K → Spectrum I)) p ≤
    polynomialEnergy (spectralCoordinate I)
      (atomicProbability (extendedMeasure I M z hR s hs hs1)
        (fun i => ⟨(extendedMeasure I M z hR s hs hs1).node i, (z i).property⟩)) p := by
  rw [polynomialEnergy_atomic_sum I M hM,
    polynomialEnergy_atomic_sum I (extendedMeasure I M z hR s hs hs1) (fun i => (z i).property)]
  rw [Fin.sum_univ_add]
  have he : (∑ i : Fin K, (extendedMeasure I M z hR s hs hs1).weight (Fin.castAdd R i) *
      (p.eval ((extendedMeasure I M z hR s hs hs1).node (Fin.castAdd R i))) ^ 2) =
      (1 - s) * ∑ i : Fin K, M.weight i * (p.eval (M.node i)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change Fin.append (fun j : Fin K => (1 - s) * M.weight j) (fun _ : Fin R => s / R)
      (Fin.castAdd R i) * (p.eval (z (Fin.castAdd R i)).val) ^ 2 = _
    rw [Fin.append_left, hz]
    ring
  rw [he]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
    mul_nonneg ((extendedMeasure I M z hR s hs hs1).positive _).le (sq_nonneg _))

/-- Christoffel information in the exact atom extension loses at most its old mass fraction.
Article: main_krylov, apC:lem:natoms.
Proof: compare every actual polynomial energy before taking the bounded-below infimum. -/
theorem christoffel_extended_lower {K R : ℕ} (I : chebyshev1.SpectralInterval)
    (M : DiscreteMeasure K) (hM : ∀ i, M.node i ∈ Set.Icc I.mu I.L)
    (z : Fin (K + R) ↪ Spectrum I)
    (hz : ∀ i : Fin K, z (Fin.castAdd R i) = ⟨M.node i, hM i⟩)
    (hR : 0 < R) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) (m : ℕ) :
    (1 - s) * christoffel m 0 (spectralCoordinate I)
      (atomicProbability M (fun i => ⟨M.node i, hM i⟩ : Fin K → Spectrum I)) ≤
    christoffel m 0 (spectralCoordinate I)
      (atomicProbability (extendedMeasure I M z hR s hs hs1)
        (fun i => ⟨(extendedMeasure I M z hR s hs hs1).node i, (z i).property⟩)) := by
  apply le_ciInf
  intro p
  exact (mul_le_mul_of_nonneg_left (christoffel_le m 0 (spectralCoordinate I) _ p)
    (by linarith)).trans (polynomialEnergy_extended_lower I M hM z hz hR s hs hs1 p.val)

/-- The mixed criterion in the exact atom extension retains the article's full power of the old mass.
Article: main_krylov, apC:lem:natoms.
Proof: apply information monotonicity under the extension and nonnegative real powers termwise. -/
theorem intervalObjective_extended_lower {K R : ℕ} (I : chebyshev1.SpectralInterval)
    (M : DiscreteMeasure K) (hM : ∀ i, M.node i ∈ Set.Icc I.mu I.L)
    (z : Fin (K + R) ↪ Spectrum I)
    (hz : ∀ i : Fin K, z (Fin.castAdd R i) = ⟨M.node i, hM i⟩)
    (hR : 0 < R) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (D : ℕ) (w : Fin D → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ : 0 ≤ γ) :
    (1 - s) ^ γ * intervalObjective I D w γ
      (atomicProbability M (fun i => ⟨M.node i, hM i⟩ : Fin K → Spectrum I)) ≤
    intervalObjective I D w γ
      (atomicProbability (extendedMeasure I M z hR s hs hs1)
        (fun i => ⟨(extendedMeasure I M z hR s hs hs1).node i, (z i).property⟩)) := by
  unfold intervalObjective mixedObjective
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp := Real.rpow_le_rpow
    (mul_nonneg (by linarith : 0 ≤ 1 - s) (christoffel_nonneg (i.val + 1) 0 _ _))
    (christoffel_extended_lower I M hM z hz hR s hs hs1 (i.val + 1)) hγ
  rw [Real.mul_rpow (by linarith : 0 ≤ 1 - s) (christoffel_nonneg _ _ _ _)] at hp
  have he := mul_le_mul_of_nonneg_left hp (hw i)
  nlinarith

/-- Every finite design is approximated in objective value by a design with exactly any larger number of atoms.
Article: main_krylov, apC:lem:natoms, the full constructive atom-padding step.
Proof: extend the old embedding in the infinite interval, assign every new atom
positive mass, and choose the total new mass explicitly from the requested tolerance. -/
theorem exists_exact_atoms_approximation {K N : ℕ} (I : chebyshev1.SpectralInterval)
    (M : DiscreteMeasure K) (hM : ∀ i, M.node i ∈ Set.Icc I.mu I.L) (hKN : K ≤ N)
    (D : ℕ) (w : Fin D → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : DiscreteMeasure N, ∃ hQ : ∀ i, Q.node i ∈ Set.Icc I.mu I.L,
      intervalObjective I D w γ
          (atomicProbability M (fun i => ⟨M.node i, hM i⟩ : Fin K → Spectrum I)) - ε <
        intervalObjective I D w γ
          (atomicProbability Q (fun i => ⟨Q.node i, hQ i⟩ : Fin N → Spectrum I)) := by
  obtain ⟨R, rfl⟩ := Nat.exists_eq_add_of_le hKN
  cases R with
  | zero => exact ⟨M, hM, sub_lt_self _ hε⟩
  | succ R =>
    obtain ⟨z, hz⟩ := exists_spectral_embedding_extension (R := R + 1) I M hM
    let A := intervalObjective I D w γ
      (atomicProbability M (fun i => ⟨M.node i, hM i⟩ : Fin K → Spectrum I))
    have hA : 0 ≤ A := mixedObjective_nonneg D w hw γ 0 _ _
    let s : ℝ := min (1 / 2) (ε / (2 * (A + 1)))
    have hs : 0 < s := lt_min (by norm_num) (div_pos hε (by positivity))
    have hs1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hloss : s * A < ε := by
      have he : ε / (2 * (A + 1)) * (A + 1) = ε / 2 := by field_simp
      have hb := mul_le_mul_of_nonneg_right
        (min_le_right (1 / 2 : ℝ) (ε / (2 * (A + 1)))) (by positivity : 0 ≤ A + 1)
      rw [he] at hb
      change s * (A + 1) ≤ ε / 2 at hb
      nlinarith
    let Q := extendedMeasure I M z (Nat.succ_pos R) s hs hs1
    have hQ : ∀ i, Q.node i ∈ Set.Icc I.mu I.L := fun i => (z i).property
    refine ⟨Q, hQ, ?_⟩
    have he := intervalObjective_extended_lower I M hM z hz (Nat.succ_pos R) s hs hs1
      D w hw hγ₀
    have hp : 1 - s ≤ (1 - s) ^ γ :=
      Real.self_le_rpow_of_le_one (by linarith) (by linarith) hγ₁
    have hl := mul_le_mul_of_nonneg_right hp hA
    have hb := hl.trans he
    change (1 - s) * A ≤ _ at hb
    change A - ε < _
    exact lt_of_lt_of_le (by nlinarith) hb

end
end krylov.Design
