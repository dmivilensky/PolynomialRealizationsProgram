import krylov.Correction.ModelError

/-!
Article: main_krylov, thm:C, actual finite data at the last RFC correction.
Use: name the real incoming gradient and collect its derived analytic domains
and actual fresh-drift coefficient in the genuine Euclidean coefficient norm.
Source: the existing actual augmented step/image families, real RFC execution
and the proved old-coordinate incoming-residual expansion.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual post-search gradient immediately before a full-memory RFC correction phase.
Use: this is the measured incoming gradient of the real model solve.
Article: main_krylov, thm:C, g′. -/
def fullPostSearch (count : ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  let m := rfcMethod fullMemory count (E := E)
  let H := methodRun m A B g k
  let d := m.direction H
  searchedGradient H.gradient d (A k d)

/-- The frozen fresh-drift coefficient in actual newest-first model coordinates.
Use: the zero head coordinate is the exact searched direction; older coordinates
are the true reference-step/operator-difference pairings derived above.
Article: main_krylov, thm:C, the unnormalized coefficient of Uᵀg′. -/
def frozenIncoming (Q : E →L[ℝ] E) (g : E) (A : ℕ → E →L[ℝ] E) (k : ℕ) :
    EuclideanSpace ℝ (Fin (k+1)) :=
  WithLp.toLp 2 (Fin.cons 0 (fun j : Fin k => inner ℝ (referenceStep Q g (k-1-j.val))
    ((A k-A (k-1-j.val)) (referenceStep Q g k))))

/-- Every actual full RFC incoming gradient and augmented step/image/model datum is analytic on its derived reference domain.
Use: supply genuine regularity to the final inverse and product estimates without assuming model expansions.
Article: main_krylov, thm:C and apD:prefix, regularity of U,H,g′.
Proof: actual prefix analyticity supplies every old step, secant and the current
direction/probe. The proved real line-step regularity supplies the incoming
gradient; finite actual pairings then assemble the true spectral-norm model. -/
theorem full_cycle_data_regular (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory count (E := E)
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let Z := fun z => probedImageBasis m (A z) (B z) (g z) k
    AnalyticAt ℝ (fun z => fullPostSearch count (A z) (B z) (g z) k) 0 ∧
      (∀ i, AnalyticAt ℝ (fun z => U z i) 0) ∧
      (∀ i, AnalyticAt ℝ (fun z => Z z i) 0) ∧
      AnalyticAt ℝ (fun z => pairModel (U z) (Z z)) 0 := by
  -- Regularity is derived from the actual positive quadratic execution before forming any inverse.
  have hm : ∀ a, CG.gradient Q (g 0) a≠0 → 0<a → 0<fullMemory a := fun _ _ ha => ha
  have ht := quadraticRFC_prefix_analytic fullMemory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun a ha => hpre a (by omega))
  have hG := (quadraticRFC_prefix_analytic fullMemory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    k (fun a ha => hpre a ha.le)).1
  have hL := (fullLineStep_regular count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).1
  let m := rfcMethod fullMemory count (E := E)
  let U := fun z => probedStepBasis m (A z) (B z) (g z) k
  let Z := fun z => probedImageBasis m (A z) (B z) (g z) k
  have hU (i : Fin (k+1)) : AnalyticAt ℝ (fun z => U z i) 0 := by
    refine Fin.cases (ht.2 k (by omega)).1 (fun j => ?_) i
    exact (ht.2 (k-1-j.val) (by omega)).2.1
  have hZ (i : Fin (k+1)) : AnalyticAt ℝ (fun z => Z z i) 0 := by
    refine Fin.cases (analytic_operator_apply (hA k) (hU 0)) (fun j => ?_) i
    exact (ht.2 (k-1-j.val) (by omega)).2.2
  refine ⟨?_,hU,hZ,?_⟩
  · apply (hG.add (analytic_operator_apply (hA k) hL)).congr
    apply Eventually.of_forall
    intro z
    simp only [fullPostSearch,fullLineStep,searchedGradient,map_smul]
    rfl
  · exact analytic_spectral_matrix _ 0 fun i j => analytic_inner (hU _) (hZ _)

/-- The actual full RFC current search curvature is nonzero on a genuine neighborhood.
Use: the exact searched-direction residual equation has its true division domain discharged.
Article: main_krylov, thm:C and apD:prefix, defined last exact search.
Proof: the actual direction is analytic with the genuine nonzero CG reference
value, whose positive quadratic curvature persists by continuity. -/
theorem full_search_curvature_eventually (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory count (E := E)
    let d := fun z => m.direction (methodRun m (A z) (B z) (g z) k)
    ∀ᶠ z in 𝓝 (0 : X), inner ℝ (d z) (A z k (d z))≠0 := by
  -- The positive reference curvature is derived from the actual CG direction.
  have hm : ∀ a, CG.gradient Q (g 0) a≠0 → 0<a → 0<fullMemory a := fun _ _ ha => ha
  let m := rfcMethod fullMemory count (E := E)
  let d := fun z => m.direction (methodRun m (A z) (B z) (g z) k)
  have hd : AnalyticAt ℝ d 0 := (full_cycle_data_regular count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).2.1 0
  have hd₀ : d 0=CG.direction Q (g 0) k := by
    dsimp only [d]
    rw [hA0,hB0]
    exact rfc_reference_direction fullMemory count Q hQ hpos (g 0) hm k
  have hc : inner ℝ (d 0) (A 0 k (d 0))≠0 := by
    rw [hd₀,hA0]
    exact (hpos _ (CG.invariant_line_pos Q hpos (g 0) k
      (CG.invariant Q hQ hpos (g 0) k (fun a ha => hpre a ha.le)) (hpre k le_rfl)).1).ne'
  exact (analytic_inner hd (analytic_operator_apply (hA k) hd)).continuousAt.eventually_ne hc

/-- The entire actual incoming coefficient vector has the genuine frozen fresh-drift expansion.
Use: close both the searched-direction coordinate and every old coordinate in the true Euclidean norm.
Article: main_krylov, thm:C, Uᵀg′=r₁+O(ω²).
Proof: the exact real line search annihilates the head coordinate on its
derived curvature domain. Each older coordinate is the proved actual
incoming-pair expansion; the finite Euclidean coordinate theorem combines them. -/
theorem full_incoming_vector_order
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0)
    (count : ℕ := 1) (hc : 0<count := by omega) :
    let m := rfcMethod fullMemory count (E := E)
    (fun z => projectedResidual (probedStepBasis m (A z) (B z) (g z) k)
      (fullPostSearch count (A z) (B z) (g z) k)-frozenIncoming Q (g 0) (A z) k) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^2) := by
  -- Assemble the actual vector through its real Euclidean coordinates, including the exactly zero head.
  apply (krylov.LinearAlgebra.euclidean_bigO_iff_entry _ _).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · apply IsBigO.of_bound 0
    filter_upwards [full_search_curvature_eventually count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre]
      with z hz
    change ‖inner ℝ _ (searchedGradient _ _ _)-(0 : ℝ)‖ ≤ _
    simp only [probedStepBasis,Fin.cons_zero,probedDirection]
    rw [searchedGradient_inner_zero _ _ _ hz,sub_zero,norm_zero]
    simp only [zero_mul,le_refl]
  · exact full_incoming_pair_order A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hk hpre
      (k-1-j.val) (by omega) count hc

end
end krylov.Correction
