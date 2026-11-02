import krylov.Correction.ChronologicalModelBasis
import krylov.Correction.OrdinarySearchCoordinates
import krylov.Correction.FullReconstruction
import krylov.Stability.WeightedCGFlags

/-!
Article: main_krylov, thm:UCq, actual observed terminal geometry.
Use: Derive the genuine full-column Gram, measured-model and quadratic image
allowances from the original recorded secants and actual observed direction solve.
Source: the proved true chronological column dictionaries, actual canonical
image conjugacy, real unit-Gram bounds and measured latest-model inequalities.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

set_option maxHeartbeats 800000 in
/-- Actual ordinary-RFC old angles, relative pair errors and true measured contamination derive every genuine terminal unit column, full Gram bound, latest-model bound and own-time normalized image error.
Use: Supply the real geometric inputs of the uniform cubic terminal response without a last-reference-energy or last-direction-comparison premise.
Article: main_krylov, thm:UCq.
Proof: The real observed inverse forces actual old-image conjugacy. Genuine chronological columns are exactly the old recorded steps followed by the raw current direction, so their true normalized Gram has the observed angle bound. Their actual last probe has zero own-time contamination. Real relative pair errors and the exact current probe give the measured latest-model distance from that same Gram; true old contamination survives its own individual length normalization.
-/
theorem ordinary_terminal_observed_geometry {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1))) {a K Cξ ε : ℝ}
    (ha : 0≤a) (hK : 1≤K) (hCξ : 0≤Cξ) (hε : 0≤ε)
    (hs : ∀ i<k, cgOperator (metricRoot base) (probedStep (rfcMethod fullMemory 1) A B g i)≠0)
    (hd : cgOperator (metricRoot base) (probedDirection (rfcMethod fullMemory 1) A B g k)≠0)
    (hC : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (methodRun (rfcMethod fullMemory 1) A B g k)))
      (windowSteps (selectedWindow fullMemory (methodRun (rfcMethod fullMemory 1) A B g k)))).det)
    (hangle : ∀ i j : Fin k, i≠j →
      |inner ℝ (unitWindow (fun i : Fin k => cgOperator (metricRoot base) (probedStep (rfcMethod fullMemory 1) A B g i.val)) i)
        (unitWindow (fun i : Fin k => cgOperator (metricRoot base) (probedStep (rfcMethod fullMemory 1) A B g i.val)) j)|≤a*ε)
    (hpair : ∀ i<k, ‖cgOperator (metricRoot base)⁻¹ (probedSecant (rfcMethod fullMemory 1) A B g i)-
      cgOperator (metricRoot base) (probedStep (rfcMethod fullMemory 1) A B g i)‖≤
        K*ε*‖cgOperator (metricRoot base) (probedStep (rfcMethod fullMemory 1) A B g i)‖)
    (hxi : ∀ i<k, ‖cgOperator (metricRoot base)⁻¹ (probedSecant (rfcMethod fullMemory 1) A B g i)-
      canonicalOperator base (A i) (cgOperator (metricRoot base) (probedStep (rfcMethod fullMemory 1) A B g i))‖≤
        Cξ*ε^2*‖cgOperator (metricRoot base) (probedStep (rfcMethod fullMemory 1) A B g i)‖)
    (hA : ‖canonicalOperator base (A k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1)))‖≤ε) :
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
    let S := primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm)
    let Y := dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm)
    let t := unitWindow S
    let z := rescaleWindow Y (fun i => ‖S i‖⁻¹)
    (∀ i, ‖t i‖=1) ∧
      ‖(fullBasisMatrix t)ᵀ*fullBasisMatrix t-1‖≤((k+1 : ℕ) : ℝ)*(a+K)*ε ∧
      ‖latest (crossGram t z)-1‖≤((k+1 : ℕ) : ℝ)*(a+2*K)*ε ∧
      ∀ i, ‖z i-canonicalOperator base (A i.val) (t i)‖≤Cξ*ε^2 := by
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
  let R := cgOperator (metricRoot base)
  let J := cgOperator (metricRoot base)⁻¹
  let s : Fin k → EuclideanSpace ℝ (Fin (k+1)) := fun i => R (probedStep m A B g i.val)
  let y : Fin k → EuclideanSpace ℝ (Fin (k+1)) := fun i => J (probedSecant m A B g i.val)
  let d := R (probedDirection m A B g k)
  let S := primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm)
  let Y := dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm)
  let t := unitWindow S
  let z := rescaleWindow Y (fun i => ‖S i‖⁻¹)
  have hK0 : 0≤K := by linarith
  have hη : 0≤K*ε := mul_nonneg hK0 hε
  have hεK : ε≤K*ε := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hε
  have hS : S=Fin.snoc s d := by
    dsimp only [S]
    rw [probedStepBasis_reverse,primalWindow_snoc]
    rfl
  have hY : Y=Fin.snoc y (J (probedProbe m A B g k)) := by
    dsimp only [Y]
    rw [probedImageBasis_reverse,dualWindow_snoc]
    rfl
  have hS0 (i : Fin (k+1)) : S i≠0 := by
    rw [hS]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hd
    · simpa only [Fin.snoc_castSucc] using hs j.val j.isLt
  have ht : ∀ i, ‖t i‖=1 := unitWindow_norm S hS0
  have ho (i : Fin k) : inner ℝ (y i) d=0 :=
    ordinary_chronological_image_conjugacy base hb A B g k hC i
  have hGram0 := unit_snoc_observed_gram s y d (fun i => hs i.val i.isLt) hd
    (mul_nonneg ha hε) hη (fun i => hpair i.val i.isLt) ho hangle
  have hGram : ‖crossGram t t-1‖≤((k+1 : ℕ) : ℝ)*(a+K)*ε := by
    change ‖crossGram (unitWindow S) (unitWindow S)-1‖≤_
    rw [hS]
    exact hGram0.trans_eq (by ring)
  have hGramT : ‖(fullBasisMatrix t)ᵀ*fullBasisMatrix t-1‖≤((k+1 : ℕ) : ℝ)*(a+K)*ε := by
    rw [transpose_mul_columnGram]
    exact hGram
  have hPairFull (i : Fin (k+1)) : ‖Y i-S i‖≤(K*ε)*‖S i‖ := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [hS,hY,Fin.snoc_last]
      have he : J (probedProbe m A B g k)=canonicalOperator base (A k) d :=
        (canonicalOperator_primal base hb (A k) (probedDirection m A B g k)).symm
      rw [he]
      have hp : ‖canonicalOperator base (A k) d-d‖≤ε*‖d‖ :=
        ((canonicalOperator base (A k)-ContinuousLinearMap.id ℝ _).le_opNorm d).trans
          (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
      exact hp.trans (mul_le_mul_of_nonneg_right hεK (norm_nonneg _))
    · simpa only [hS,hY,Fin.snoc_castSucc] using hpair j.val j.isLt
  have hModel0 := latest_crossGram_gram_distance t z ht hη
    (unitWindow_pair_error S Y hS0 hPairFull)
  have hModel : ‖latest (crossGram t z)-1‖≤((k+1 : ℕ) : ℝ)*(a+2*K)*ε := by
    calc
      _ = ‖(latest (crossGram t z)-crossGram t t)+(crossGram t t-1)‖ := by congr 1; abel
      _ ≤ ‖latest (crossGram t z)-crossGram t t‖+‖crossGram t t-1‖ := norm_add_le _ _
      _ ≤ ((k+1 : ℕ) : ℝ)*(K*ε)+((k+1 : ℕ) : ℝ)*(a+K)*ε := add_le_add hModel0 hGram
      _ = _ := by ring
  have hXi := normalized_chronological_contamination base hb m A B g k
    (mul_nonneg hCξ (sq_nonneg ε)) hs hd hxi
  dsimp only
  exact ⟨ht,hGramT,hModel,hXi⟩

end
end krylov.Correction
