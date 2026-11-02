import krylov.XR.XRFCFunction
import krylov.Correction.ChronologicalCorrection
import krylov.Methods.VirtualCoordinates

/-!
Article: main_krylov, alg:xrfc and lem:xr-local, exact storage dictionary.
Use: the native chronological full-memory step/secant observations give
exactly the original newest-first XRFC virtual correction, extrapolated
gradient and conjugacy direction. Source: genuine observed-list reversal
and bijective reindexing of the actual finite inverse solve.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Correction
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual observed pair transcript in the original policy's
newest-first storage order. -/
def xrfcNewestPairs (W : List (PairObservation E)) : List (E × E) := (secantPairs W).reverse

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem xrfcNewestPairs_length (W : List (PairObservation E)) :
    (xrfcNewestPairs W).length = W.length := by simp only [xrfcNewestPairs, List.length_reverse, secantPairs, List.length_map]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Actual list reversal reads precisely the reverse chronological pair;
only its true finite length cast changes. -/
theorem xrfcNewestPairs_get (W : List (PairObservation E)) (i : Fin (xrfcNewestPairs W).length) :
    (xrfcNewestPairs W).get i =
      (storedSteps W (finCongr (xrfcNewestPairs_length W) i).rev,
        storedImages W (finCongr (xrfcNewestPairs_length W) i).rev) := by
  change ((secantPairs W).reverse)[i.val] = _
  rw [List.getElem_reverse]
  simp only [secantPairs, List.getElem_map, storedSteps, storedImages, List.get_eq_getElem, Fin.val_rev]
  have he : W.length - 1 - i.val = W.length - ((finCongr (xrfcNewestPairs_length W) i).val + 1) := by
    change W.length - 1 - i.val = W.length - (i.val + 1)
    omega
  simp only [List.length_map]
  simp only [he]

/-- Physical model solves and virtual gradients agree exactly between
chronological native lists and the original XRFC history convention. -/
theorem xrfcNewestPairs_virtual (W : List (PairObservation E)) (g : E) :
    virtualCorrection (xrfcNewestPairs W) g =
      modelVirtualCorrection (storedSteps W) (storedModel W) g ∧
    virtualGradient (xrfcNewestPairs W) g =
      modelVirtualGradient (storedSteps W) (storedImages W) (storedModel W) g := by
  let s := storedSteps W
  let y := storedImages W
  let e := finCongr (xrfcNewestPairs_length W)
  have hs : windowSteps (xrfcNewestPairs W) = (s ∘ Fin.revPerm) ∘ e := by
    funext i
    exact congrArg Prod.fst (xrfcNewestPairs_get W i)
  have hy : windowImages (xrfcNewestPairs W) = (y ∘ Fin.revPerm) ∘ e := by
    funext i
    exact congrArg Prod.snd (xrfcNewestPairs_get W i)
  have hv := virtualWindow_coordinates (xrfcNewestPairs W) (xrfcNewestPairs_length W)
    (s ∘ Fin.revPerm) (y ∘ Fin.revPerm) hs hy g
  have hm : pairModel (s ∘ Fin.revPerm) (y ∘ Fin.revPerm) =
      (latest (crossGram s y)).submatrix Fin.revPerm Fin.revPerm := by
    have hh := congrArg (fun M : Matrix (Fin W.length) (Fin W.length) ℝ =>
      M.submatrix Fin.revPerm Fin.revPerm) (latest_crossGram_reverse_pairModel s y)
    have he : (Fin.revPerm : Fin W.length ≃ Fin W.length) ∘ Fin.revPerm = id := by
      funext i
      exact Fin.rev_rev i
    rw [submatrix_submatrix, he, submatrix_id_id] at hh
    exact hh
  constructor
  · exact hv.1.trans (chronological_modelCorrection s y g).symm
  · rw [hv.2, hm]
    unfold modelVirtualGradient
    congr 1
    unfold combine
    simp only [modelCoefficients_reindex, Function.comp_apply]
    exact Equiv.sum_comp (Fin.revPerm (n := W.length))
      (fun i => modelCoefficients s (latest (crossGram s y)) g i • y i)

/-- The actual newest-first conjugacy solve is the same physical
chronological solve, including totalized singular data. -/
theorem xrfcNewestPairs_direction (W : List (PairObservation E)) (g : E) :
    windowDirection (xrfcNewestPairs W) g = conjugacyDirection (storedSteps W) (storedImages W) g := by
  let e := (finCongr (xrfcNewestPairs_length W)).trans (Fin.revPerm (n := W.length))
  have hs : windowSteps (xrfcNewestPairs W) = storedSteps W ∘ e := by
    funext i
    exact congrArg Prod.fst (xrfcNewestPairs_get W i)
  have hy : windowImages (xrfcNewestPairs W) = storedImages W ∘ e := by
    funext i
    exact congrArg Prod.snd (xrfcNewestPairs_get W i)
  change conjugacyDirection (windowSteps _) (windowImages _) g = _
  rw [hs, hy, conjugacyDirection_reindex]

/-- Both actual XRFC implementations make the same physical query
whenever they read the same real observations and the same trial scalar. -/
theorem fullVirtualStep_eq_xrfcStep {n : ℕ} (P : Parameters) (hoff : P.valuesEnabled = false)
    (S : State (EuclideanSpace ℝ (Fin n))) (H : History (EuclideanSpace ℝ (Fin n)))
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hpairs : H.pairs = xrfcNewestPairs S.pairs) (hg : H.gradient = S.gradient)
    (ht : trial H = algorithmTrialParameter P S) :
    fullVirtualStep P (algorithmTrialParameter P) S = (xrfcMethod fullMemory trial).step H := by
  classical
  have hv := xrfcNewestPairs_virtual S.pairs S.gradient
  have hd := xrfcNewestPairs_direction S.pairs
  change fullVirtualStep P (algorithmTrialParameter P) S =
    virtualCorrection (selectedWindow fullMemory H) H.gradient +
      trial H • windowDirection (selectedWindow fullMemory H)
        (virtualGradient (selectedWindow fullMemory H) H.gradient)
  rw [selectedWindow_full, hpairs, hg, ht, hv.1, hv.2, hd]
  unfold fullVirtualStep fullVirtualCorrection fullVirtualSelectedModel
  simp only [hoff, Bool.false_eq_true, ite_false]
  split_ifs with hempty
  · have he : S.pairs = [] := List.length_eq_zero_iff.mp hempty
    rw [he]
    have hcorr : modelVirtualCorrection (storedSteps ([] : List (PairObservation _)))
        (storedModel []) S.gradient = 0 := by
      unfold modelVirtualCorrection combine
      exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
    have hvg : modelVirtualGradient (storedSteps ([] : List (PairObservation _))) (storedImages [])
        (storedModel []) S.gradient = S.gradient := by
      change S.gradient + (∑ i : Fin 0, modelCoefficients (storedSteps []) (storedModel []) S.gradient i •
        storedImages [] i) = S.gradient
      rw [Finset.sum_eq_zero (fun i _ => Fin.elim0 i), add_zero]
    have hdir : conjugacyDirection (storedSteps ([] : List (PairObservation _))) (storedImages [])
        S.gradient = -S.gradient := by
      change -S.gradient + (∑ i : Fin 0,
        conjugacyCoefficients (storedSteps []) (storedImages []) S.gradient i • storedSteps [] i) = -S.gradient
      rw [Finset.sum_eq_zero (fun i _ => Fin.elim0 i), add_zero]
    rw [hcorr, hvg, hdir, zero_add]
  · rfl

end
end krylov.XR
