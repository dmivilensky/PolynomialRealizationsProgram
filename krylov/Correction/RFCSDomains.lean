import krylov.Correction.RFCSOperatorTube
import krylov.Stability.CompactEventual

/-!
Article: main_krylov, thm:RFCS, genuine uniform inverse/search/gate domains.
Use: Derive common compact-reference domains for the actual old conjugacy
inverse, augmented latest-model inverse, positive genuine probe curvature
and every nonempty actual observed defect gate.
Source: original measured-prefix analyticity and quadratic reference domains,
real positive CG curvature, actual observed-gate continuity and the proved
compact neighborhood tube. Empty old windows are included.
-/

namespace krylov.Correction
noncomputable section
open Set Filter Topology krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The actual retained full-memory RFC-S total steps in their genuine fixed finite age coordinates.
Use: Expose the true old conjugacy and latest-model coefficient matrices.
Article: main_krylov, thm:RFCS, genuine uniform source inverse and gate domains.
-/
def rfcsDirectOldSteps (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) (j : Fin (min (fullMemory i) i)) :=
  rfcSStep fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 (i-1-j.val)

/-- The actual retained consecutive-gradient secants of the direct-source RFC-S run in the same genuine finite age coordinates.
Use: Keep the inverse and gate domains tied to true measured data.
Article: main_krylov, thm:RFCS, genuine uniform source inverse and gate domains.
-/
def rfcsDirectOldImages (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) (j : Fin (min (fullMemory i) i)) :=
  rfcSSecant fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 (i-1-j.val)

/-- The genuine nonsingular old and augmented model solves, positive probe curvature and actual nonempty observed defect-gate acceptance at one RFC-S iteration.
Use: State actual well-definedness before applying local source expansions.
Article: main_krylov, thm:RFCS, genuine uniform source inverse and gate domains.
-/
def rfcsDirectIterationDomain (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) : Prop :=
  let S := rfcsDirectOldSteps base i z
  let Y := rfcsDirectOldImages base i z
  let d := rfcSDirection fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i
  let p := rfcsDirectProbe base z i d
  (crossGram Y S).det≠0 ∧ (pairModel (Fin.cons d S) (Fin.cons p Y)).det≠0 ∧
    0 < inner ℝ d p ∧
    (0 < i → selectedWindow fullMemory
      (rfcSRun fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i)≠[] ∧
      ‖windowDefect (selectedWindow fullMemory
        (rfcSRun fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i))‖<1)

/-- Every actual RFC-S iteration near a full-active reference has genuine inverse domains, positive actual probe curvature and accepted nonempty observed defect gate on a proved neighborhood.
Use: Derive actual well-defined source domains from real reference execution, rather than impose them as trajectory hypotheses.
Article: main_krylov, thm:RFCS, genuine uniform source inverse and gate domains.
Proof: Actual analytic measured steps and secants give continuous true determinants. The original positive quadratic transcript proves their nonzero reference values and positive genuine curvature. The proved real measured-gate neighborhood supplies the accepted branch.
-/
theorem rfcs_direct_iteration_domain_eventually (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g)
    (i : ℕ) (hi : i<k+1) :
    ∀ᶠ z in 𝓝 (g,(0 : RFCSOperatorParameters (k+1))), rfcsDirectIterationDomain base i z := by
  let Q := cgOperator base
  have hQ := cgOperator_positive base hb
  have hop := rfcs_direct_operators_zero base g
  have ht := rfcs_direct_prefix_analytic base hb g (k+1) hN
  let S := rfcsDirectOldSteps base i
  let Y := rfcsDirectOldImages base i
  let d := fun z => rfcSDirection fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i
  let p := fun z => rfcsDirectProbe base z i (d z)
  have hS (j : Fin (min (fullMemory i) i)) : AnalyticAt ℝ (fun z => S z j) (g,0) := by
    have hj := j.isLt
    exact (ht.2 (i-1-j.val) (by omega)).2.1
  have hY (j : Fin (min (fullMemory i) i)) : AnalyticAt ℝ (fun z => Y z j) (g,0) := by
    have hj := j.isLt
    exact (ht.2 (i-1-j.val) (by omega)).2.2
  have hd : AnalyticAt ℝ d (g,0) := (ht.2 i hi).1
  have hp : AnalyticAt ℝ p (g,0) := analytic_operator_apply ((rfcs_direct_operators_analytic base g).2 i) hd
  have hd₀ : d (g,0)=CG.direction Q g i := by
    dsimp only [d]
    rw [hop.1,hop.2,(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g i).2.1]
    exact rfc_reference_direction fullMemory 1 Q hQ.1 hQ.2 g (fun _ _ hj => hj) i
  have hp₀ : p (g,0)=Q (CG.direction Q g i) := by dsimp only [p]; rw [hop.2,hd₀]
  have hpre (j : ℕ) (hj : j ≤ i) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j ((hj.trans_lt hi).trans_le hN)
  have hdom := rfc_reference_coordinate_domains fullMemory 1 Q hQ.1 hQ.2 g (fun _ _ hj => hj) i hpre
  have hS₀ : S (g,0)=(fun j : Fin (min (fullMemory i) i) => probedStep (rfcMethod fullMemory 1) (fun _ => Q) (fun _ => Q) g (i-1-j.val)) := by
    funext j
    dsimp only [S,rfcsDirectOldSteps]
    rw [hop.1,hop.2,(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g _).2.2.1]
  have hY₀ : Y (g,0)=(fun j : Fin (min (fullMemory i) i) => probedSecant (rfcMethod fullMemory 1) (fun _ => Q) (fun _ => Q) g (i-1-j.val)) := by
    funext j
    dsimp only [Y,rfcsDirectOldImages]
    rw [hop.1,hop.2,(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g _).2.2.2]
  have hC₀ : (crossGram (Y (g,0)) (S (g,0))).det≠0 := by
    rw [hY₀,hS₀]
    exact hdom.1
  have hM₀ : (pairModel (Fin.cons (d (g,0)) (S (g,0))) (Fin.cons (p (g,0)) (Y (g,0)))).det≠0 := by
    rw [hd₀,hp₀,hS₀,hY₀]
    exact hdom.2
  -- The actual finite measured determinants remain nonzero on their true reference neighborhoods.
  have hC := (analytic_matrix_det (fun z => crossGram (Y z) (S z)) (g,0)
    (fun a b => analytic_inner (hY a) (hS b))).continuousAt.eventually_ne hC₀
  have hU (j : Fin (min (fullMemory i) i+1)) : AnalyticAt ℝ (fun z => (Fin.cons (d z) (S z) : Fin (min (fullMemory i) i+1) → _) j) (g,0) :=
    Fin.cases hd hS j
  have hZ (j : Fin (min (fullMemory i) i+1)) : AnalyticAt ℝ (fun z => (Fin.cons (p z) (Y z) : Fin (min (fullMemory i) i+1) → _) j) (g,0) :=
    Fin.cases hp hY j
  have hM := (analytic_matrix_det (fun z => pairModel (Fin.cons (d z) (S z)) (Fin.cons (p z) (Y z))) (g,0)
    (fun a b => analytic_inner (hU _) (hZ _))).continuousAt.eventually_ne hM₀
  have hcurv₀ : 0 < inner ℝ (d (g,0)) (p (g,0)) := by
    rw [hd₀,hp₀]
    exact hQ.2 _ (CG.invariant_line_pos Q hQ.2 g i
      (CG.invariant Q hQ.1 hQ.2 g i (fun j hj => hpre j hj.le)) (hpre i le_rfl)).1
  have hcurv := (analytic_inner hd hp).continuousAt.eventually (lt_mem_nhds hcurv₀)
  have hgate : ∀ᶠ z in 𝓝 (g,(0 : RFCSOperatorParameters (k+1))),
      0 < i → selectedWindow fullMemory (rfcSRun fullMemory (rfcsDirectProbe base z)
        (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i)≠[] ∧
      ‖windowDefect (selectedWindow fullMemory (rfcSRun fullMemory (rfcsDirectProbe base z)
        (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i))‖<1 := by
    by_cases hpos : 0 < i
    · have hn (j : Fin (min (fullMemory i) i)) :
          rfcSStep fullMemory (rfcsDirectProbe base (g,0)) (rfcsDirectLine base (g,0)) (rfcsDirectLine base (g,0)) g (i-1-j.val)≠0 := by
        have hj := j.isLt
        rw [hop.1,hop.2,(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g _).2.2.1,
          (rfc_reference_pair fullMemory 1 Q hQ.1 hQ.2 g (fun _ _ hj => hj) _).1]
        obtain ⟨hd',hl',_⟩ := CG.invariant_line_pos Q hQ.2 g (i-1-j.val)
          (CG.invariant Q hQ.1 hQ.2 g _ (fun j' hj' => hpre j' (by omega))) (hpre _ (by omega))
        exact smul_ne_zero hl'.ne' hd'
      have hyQ (j : Fin (min (fullMemory i) i)) :
          rfcSSecant fullMemory (rfcsDirectProbe base (g,0)) (rfcsDirectLine base (g,0)) (rfcsDirectLine base (g,0)) g (i-1-j.val)=
          Q (rfcSStep fullMemory (rfcsDirectProbe base (g,0)) (rfcsDirectLine base (g,0)) (rfcsDirectLine base (g,0)) g (i-1-j.val)) := by
        rw [hop.1,hop.2]
        exact rfcSSecant_exact_segment fullMemory (fun _ => Q) (fun _ => Q) g _
      have he := retained_history_gate_eventually fullMemory
        (fun z => rfcSRun fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i)
        (fun z => rfcSStep fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1)
        (fun z => rfcSSecant fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1)
        (g,0) i (fun _ => rfcSRun_pairs _ _ _ _ _ _) (fun j hj => (ht.2 j (hj.trans hi)).2.1.continuousAt)
        (fun j hj => (ht.2 j (hj.trans hi)).2.2.continuousAt) Q hQ.1 hQ.2 hn hyQ (by simpa only [fullMemory,Nat.min_self] using hpos.ne')
      filter_upwards [he] with z hz _
      exact hz
    · exact Eventually.of_forall fun _ hi' => (hpos hi').elim
  filter_upwards [hC,hM,hcurv,hgate] with z hc hm hcu hga
  exact ⟨hc,hm,hcu,hga⟩

/-- One full compact-reference/source tube gives the genuine inverse, positive-curvature and observed-gate domains of every actual RFC-S iteration simultaneously.
Use: Uniformly justify all real nonlinear source solves and branches after localization and operator realization.
Article: main_krylov, thm:RFCS, genuine uniform source inverse and gate domains.
Proof: Intersect the finitely many proved genuine iteration neighborhoods and apply the compact reference neighborhood tube.
-/
theorem compact_rfcs_direct_domains (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) :
    ∃ δ : ℝ, 0<δ ∧ ∀ g∈K, ∀ v : EuclideanSpace ℝ (Fin (k+1)),
      ∀ Θ : RFCSOperatorParameters (k+1), ‖(v,Θ)‖≤δ → ∀ i<k+1,
      rfcsDirectIterationDomain base i (g+v,Θ) := by
  obtain ⟨δ,hδ,hbound⟩ := compact_reference_eventual_tube
    (fun z => ∀ i : Fin (k+1), rfcsDirectIterationDomain base i.val z) K hK (by
      intro g hg
      exact Filter.eventually_all.mpr fun i => rfcs_direct_iteration_domain_eventually base hb g (hN g hg) i.val i.isLt)
  exact ⟨δ,hδ,fun g hg v Θ hΘ i hi => hbound g hg v Θ hΘ ⟨i,hi⟩⟩

end
end krylov.Correction
