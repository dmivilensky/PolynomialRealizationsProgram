import krylov.XR.LocalHistoryChart
import krylov.Methods.WindowCoordinates
import krylov.Methods.DirectionReindex

/-!
Article: main_krylov, lem:xr-local, exact native endpoint-chart dictionary.
Use: identify the real list-based full-memory XRFC/F solve with the C^r
endpoint-coordinate query, including transported covectors and the exact
value diagonal. Source: actual observed arrays and bijective reindexing of
the genuine totalized inverse solve. No regularity or inverse premise is
needed for these exact identities.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual chronological records represented by an endpoint chart,
including each true current-anchor transported covector. -/
def endpointObservations {k : ℕ} (C : EndpointChart E k) : List (PairObservation E) :=
  List.ofFn (fun i : Fin k =>
    { step := endpointStep C i
      image := endpointImage C i
      anchor := C.1 i.castSucc
      anchorPairing := inner ℝ (endpointImage C i) (C.1 (Fin.last k) - C.1 i.castSucc)
      valueDefect := endpointDefect C i })

theorem endpointObservations_length {k : ℕ} (C : EndpointChart E k) :
    (endpointObservations C).length = k := List.length_ofFn

/-- An actual stored chronological record is its endpoint-chart record. -/
theorem endpointObservations_get {k : ℕ} (C : EndpointChart E k)
    (i : Fin (endpointObservations C).length) :
    (endpointObservations C).get i =
      { step := endpointStep C (finCongr (endpointObservations_length C) i)
        image := endpointImage C (finCongr (endpointObservations_length C) i)
        anchor := C.1 (finCongr (endpointObservations_length C) i).castSucc
        anchorPairing := inner ℝ (endpointImage C (finCongr (endpointObservations_length C) i))
          (C.1 (Fin.last k) - C.1 (finCongr (endpointObservations_length C) i).castSucc)
        valueDefect := endpointDefect C (finCongr (endpointObservations_length C) i) } := by
  change (endpointObservations C)[i.val] = _
  simp only [endpointObservations, List.getElem_ofFn]
  rfl

theorem endpointObservations_steps {k : ℕ} (C : EndpointChart E k) :
    storedSteps (endpointObservations C) = endpointStep C ∘ finCongr (endpointObservations_length C) := by
  funext i
  exact congrArg PairObservation.step (endpointObservations_get C i)

theorem endpointObservations_images {k : ℕ} (C : EndpointChart E k) :
    storedImages (endpointObservations C) = endpointImage C ∘ finCongr (endpointObservations_length C) := by
  funext i
  exact congrArg PairObservation.image (endpointObservations_get C i)

/-- The real observed raw pair matrix is exactly its endpoint-coordinate
matrix, under the sole genuine list-length cast. -/
theorem endpointObservations_pairing {k : ℕ} (C : EndpointChart E k) :
    storedPairing (endpointObservations C) =
      (crossGram (endpointStep C) (endpointImage C)).submatrix
        (finCongr (endpointObservations_length C)) (finCongr (endpointObservations_length C)) := by
  rw [storedPairing, endpointObservations_steps, endpointObservations_images]
  rfl

/-- The literal latest and F models reindex to the exact endpoint model. -/
theorem endpointObservations_model {n k : ℕ} (P : Parameters)
    (C : EndpointChart (EuclideanSpace ℝ (Fin n)) k) :
    fullVirtualSelectedModel P (endpointObservations C) =
      (endpointVirtualModel P.valuesEnabled C).submatrix
        (finCongr (endpointObservations_length C)) (finCongr (endpointObservations_length C)) := by
  classical
  let e := finCongr (endpointObservations_length C)
  have hmin (i j : Fin (endpointObservations C).length) : e (min i j) = min (e i) (e j) := by
    apply Fin.ext
    rfl
  have hmax (i j : Fin (endpointObservations C).length) : e (max i j) = max (e i) (e j) := by
    apply Fin.ext
    rfl
  have hmodel : storedModel (endpointObservations C) =
      (latest (crossGram (endpointStep C) (endpointImage C))).submatrix e e := by
    ext i j
    simp only [storedModel, storedPairing, latest, crossGram, endpointObservations_steps,
      endpointObservations_images, Function.comp_apply, Matrix.submatrix_apply]
    change inner ℝ (endpointStep C (e (min i j))) (endpointImage C (e (max i j))) = _
    rw [hmin, hmax]
  have hsplit (i : Fin (endpointObservations C).length) :
      storedSplit (endpointObservations C) i = endpointSplit C (e i) := by
    unfold storedSplit storedPairing crossGram
    rw [endpointObservations_get, endpointObservations_steps, endpointObservations_images]
    rfl
  ext i j
  by_cases hvalues : P.valuesEnabled = true
  · rw [fullVirtualSelectedModel, ite_eq_left hvalues, storedExactValueModel, hmodel]
    simp only [endpointVirtualModel, hvalues, ite_true, Matrix.sub_apply,
      Matrix.submatrix_apply]
    congr 1
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq, hsplit, endpointObservations_get]
      rfl
    · have heij : e i ≠ e j := e.injective.ne hij
      rw [diagonal_apply_ne _ hij]
      change 0 = diagonal (fun i => 12 * endpointSplit C i * endpointDefect C i) (e i) (e j)
      exact (diagonal_apply_ne _ heij).symm
  · have hoff : P.valuesEnabled = false := Bool.eq_false_iff.mpr hvalues
    rw [fullVirtualSelectedModel, ite_eq_right hvalues, hmodel]
    simp only [endpointVirtualModel, hoff, Bool.false_eq_true, ite_false, diagonal_zero,
      sub_zero]
    rfl

/-- The full native list solve is exactly the endpoint-coordinate
physical correction, for both F flags and even outside inverse domains. -/
theorem fullVirtualCorrection_endpoint {n k : ℕ} (P : Parameters)
    (C : EndpointChart (EuclideanSpace ℝ (Fin n)) k)
    (S : State (EuclideanSpace ℝ (Fin n))) (hW : S.pairs = endpointObservations C)
    (hg : S.gradient = C.2.2 (Fin.last k)) :
    fullVirtualCorrection P S = modelVirtualCorrection (endpointStep C)
      (endpointVirtualModel P.valuesEnabled C) (C.2.2 (Fin.last k)) := by
  unfold fullVirtualCorrection modelVirtualCorrection
  rw [hW, hg, endpointObservations_steps, endpointObservations_model]
  exact modelCorrection_reindex _ _ _ _

/-- Complete native full-memory XRFC/F queries have exactly the genuine
C^r endpoint formula. Every assumed equality here is an input-coordinate
dictionary; no query output, smoothness or rate is postulated. -/
theorem fullVirtualStep_endpoint {n k : ℕ} (P : Parameters)
    (C : EndpointChart (EuclideanSpace ℝ (Fin n)) k)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ) (t : EndpointChart (EuclideanSpace ℝ (Fin n)) k → ℝ)
    (hW : S.pairs = endpointObservations C) (hx : S.point = C.1 (Fin.last k))
    (hg : S.gradient = C.2.2 (Fin.last k)) (ht : trial S = t C) :
    S.point + fullVirtualStep P trial S = endpointVirtualQuery P.valuesEnabled t C := by
  classical
  have hc := fullVirtualCorrection_endpoint P C S hW hg
  have hd : modelDirection (storedSteps S.pairs) (storedImages S.pairs)
      (fullVirtualSelectedModel P S.pairs) S.gradient =
      modelDirection (endpointStep C) (endpointImage C) (endpointVirtualModel P.valuesEnabled C)
        (C.2.2 (Fin.last k)) := by
    unfold modelDirection modelVirtualGradient
    rw [hW, hg, endpointObservations_steps, endpointObservations_images, endpointObservations_model]
    have hw := modelCoefficients_reindex (finCongr (endpointObservations_length C))
      (endpointStep C) (endpointVirtualModel P.valuesEnabled C) (C.2.2 (Fin.last k))
    have hy : combine (endpointImage C ∘ finCongr (endpointObservations_length C))
        (modelCoefficients (endpointStep C ∘ finCongr (endpointObservations_length C))
          ((endpointVirtualModel P.valuesEnabled C).submatrix
            (finCongr (endpointObservations_length C)) (finCongr (endpointObservations_length C)))
          (C.2.2 (Fin.last k))) =
        combine (endpointImage C)
          (modelCoefficients (endpointStep C) (endpointVirtualModel P.valuesEnabled C) (C.2.2 (Fin.last k))) := by
      unfold combine
      simp only [hw, Function.comp_apply]
      exact Equiv.sum_comp (finCongr (endpointObservations_length C))
        (fun i : Fin k => modelCoefficients (endpointStep C) (endpointVirtualModel P.valuesEnabled C)
          (C.2.2 (Fin.last k)) i • endpointImage C i)
    rw [hy, conjugacyDirection_reindex]
  unfold fullVirtualStep
  split_ifs with hempty
  · have hk : k = 0 := by rw [hW, endpointObservations_length] at hempty; exact hempty
    subst k
    rw [hx, hg, ht]
    simp only [endpointVirtualQuery, modelVirtualCorrection, modelDirection, modelVirtualGradient,
      conjugacyDirection, combine, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  · rw [hc, hd, ht, hx]
    exact add_assoc _ _ _ |>.symm

end
end krylov.XR
