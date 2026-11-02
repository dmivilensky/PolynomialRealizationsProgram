import krylov.Correction.ProbedConjugacy
import krylov.Correction.PairingOrders

/-!
Article: main_krylov, thm:C and apD:prefix, the actual incoming fresh residual.
Use: derive the first-order pre-correction residual from the real RFC run,
keeping the old recorded steps and the line displacement distinct.
Source: actual local conjugacy, actual quadratic pair-defect orders and the
proved first-order replacement calculus for genuine adaptive outer factors.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine exact-search displacement before the actual RFC correction phase.
Use: fresh-defect formulas use the searched line rather than the total recorded step.
Article: main_krylov, apD:prefix, σ_k^ℓ=α_kd_k. -/
def fullLineStep (count : ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  let m := rfcMethod fullMemory count (E := E)
  let H := methodRun m A B g k
  let d := m.direction H
  lineLength H.gradient d (A k d) • d

/-- The actual full-memory RFC line displacement is analytic and has the genuine CG reference value.
Use: discharge both regularity and reference-value premises of fresh-defect outer-factor replacement.
Article: main_krylov, apD:prefix, actual line-step perturbation.
Proof: the executed prefix supplies analytic gradients and directions. True
quadratic CG positivity makes the real line curvature nonzero; analytic division
gives the actual line displacement, and quadratic execution identifies its value. -/
theorem fullLineStep_regular (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    AnalyticAt ℝ (fun z => fullLineStep count (A z) (B z) (g z) k) 0 ∧
      fullLineStep count (A 0) (B 0) (g 0) k=referenceStep Q (g 0) k := by
  -- Establish the genuine current curvature before differentiating the line quotient.
  let m := rfcMethod fullMemory count (E := E)
  let H := fun z => methodRun m (A z) (B z) (g z) k
  let d := fun z => m.direction (H z)
  have hm : ∀ j, CG.gradient Q (g 0) j≠0 → 0<j → 0<fullMemory j := fun _ _ hj => hj
  have ht := quadraticRFC_prefix_analytic fullMemory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun i hi => hpre i (by omega))
  have hG := (quadraticRFC_prefix_analytic fullMemory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    k (fun i hi => hpre i hi.le)).1
  have hd : AnalyticAt ℝ d 0 := (ht.2 k (by omega)).1
  have hz := analytic_operator_apply (hA k) hd
  have hd₀ : d 0=CG.direction Q (g 0) k := by
    dsimp only [d,H]
    rw [hA0,hB0]
    exact rfc_reference_direction fullMemory count Q hQ hpos (g 0) hm k
  have hG₀ : (H 0).gradient=CG.gradient Q (g 0) k := by
    dsimp only [H]
    rw [hA0,hB0]
    exact (rfcMethod_static fullMemory count Q hQ hpos (g 0) hm k).1
  have hc : inner ℝ (d 0) (A 0 k (d 0))≠0 := by
    rw [hd₀,hA0]
    exact (hpos _ (CG.invariant_line_pos Q hpos (g 0) k
      (CG.invariant Q hQ hpos (g 0) k (fun i hi => hpre i hi.le)) (hpre k le_rfl)).1).ne'
  refine ⟨((analytic_inner hd hG).neg.div (analytic_inner hd hz) hc).smul hd,?_⟩
  change lineLength (H 0).gradient (d 0) (A 0 k (d 0)) • d 0=_
  rw [hG₀,hd₀,hA0]
  rfl

/-- The actual old-coordinate incoming RFC residual has its frozen fresh-drift formula with a quadratic remainder.
Use: the printed fresh defect is derived from genuine executed probes, searches,
recorded pairs and earlier corrections rather than supplied as an expansion premise.
Article: main_krylov, thm:C, C^(−1/2)Uᵀg′=√c Qᵀf̂+O(ω²), old coordinates.
Proof: exact executed conjugacy splits the residual into the old projected
gradient, a fresh operator-difference pairing and the real pair defect. The first
and third terms have quadratic order; replacing the two actual outer vectors in
the middle term by their genuine CG reference steps costs quadratic order too. -/
theorem full_incoming_pair_order
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0)
    (i : ℕ) (hi : i<k) (count : ℕ := 1) (hc : 0<count := by omega) :
    let m := rfcMethod fullMemory count (E := E)
    let H := fun z => methodRun m (A z) (B z) (g z) k
    let d := fun z => m.direction (H z)
    (fun z => inner ℝ (probedStep m (A z) (B z) (g z) i)
      (searchedGradient (H z).gradient (d z) (A z k (d z)))-
      inner ℝ (referenceStep Q (g 0) i) ((A z k-A z i) (referenceStep Q (g 0) k))) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^2) := by
  -- Keep the three actual residual contributions separate until their orders are proved.
  let m := rfcMethod fullMemory count (E := E)
  let H := fun z => methodRun m (A z) (B z) (g z) k
  let s := fun z => probedStep m (A z) (B z) (g z) i
  let line := fun z => fullLineStep count (A z) (B z) (g z) k
  let T := fun z => A z k-A z i
  let xi := fun z => probedSecant m (A z) (B z) (g z) i-A z i (s z)
  have hm : ∀ j, CG.gradient Q (g 0) j≠0 → 0<j → 0<fullMemory j := fun _ _ hj => hj
  have ht := quadraticRFC_prefix_analytic fullMemory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun j hj => hpre j (by omega))
  have hs : AnalyticAt ℝ s 0 := (ht.2 i (by omega)).2.1
  have hs₀ : s 0=referenceStep Q (g 0) i := by
    dsimp only [s]
    rw [hA0,hB0]
    exact (rfc_reference_pair fullMemory count Q hQ hpos (g 0) hm i).1
  have hl := fullLineStep_regular count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre
  have hT : T =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    have he := analytic_reference_order T ((hA k).sub (hA i))
    have hz : T 0=0 := by dsimp only [T]; rw [hA0,sub_self]
    simpa only [hz,sub_zero] using he
  have hsn : (fun z => s z-referenceStep Q (g 0) i) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [hs₀] using analytic_reference_order s hs
  have hln : (fun z => line z-referenceStep Q (g 0) k) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [line,hl.2] using analytic_reference_order line hl.1
  have hfrozen := pairing_reference_order s line (referenceStep Q (g 0) i)
    (referenceStep Q (g 0) k) T (fun z => ‖z‖)
      (by simpa only [norm_zero] using continuous_norm.tendsto (0 : X)) hsn hln hT
  have hold := full_recorded_pair_order count A B g hA hB hg Q hA0 hB0 hQ hpos (k-1)
    (fun j hj => hpre j (by omega)) i (by omega)
  have hold' : (fun z => inner ℝ (s z) (H z).gradient) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    simpa only [show k-1+1=k by omega,probedGradient,H,s,m,Nat.reduceAdd] using hold.trans (norm_pow_order_mono (by omega : 2≤count+1))
  have hxi := (quadraticRFC_pair_orders fullMemory count A B g hA hB hg Q hA0 hB0 hQ hpos hm i
    (fun j hj => hpre j (by omega))).2
  have hbad := inner_order xi line (fun z => ‖z‖^2) (fun _ => 1) hxi (hl.1.continuousAt.tendsto.isBigO_one ℝ)
  have hbad' : (fun z => inner ℝ (xi z) (line z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    simpa only [mul_one] using hbad
  apply ((hold'.add hfrozen).sub hbad').congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [full_search_pair_identity_eventually count A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hpre]
    with z hz
  rw [hz i hi]
  dsimp only [T,line,fullLineStep,xi,s,H]
  abel

end
end krylov.Correction
