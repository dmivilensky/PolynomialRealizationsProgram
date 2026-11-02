import krylov.Cancellation.DCEstimateRegularity
import krylov.Cancellation.ObservedWindowDomain
import krylov.Cancellation.FrozenResidualProducts
import krylov.Cancellation.ResidualPropagation
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), complete actual compact C-one residual expansion.
Use: expand the true returned residual using actual fresh defects and searched
lengths, freezing only the genuine reference values of the observed estimates.
Source: native DC smooth coefficient compilation, true quadratic consistency,
actual retained inverse domains and the proved compact C-one product estimate.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- The original exact-search DC line length on its actual observed history.
Use: the source frozen estimate formula retains this real varying searched length.
Article: main_krylov, thm:dcs(c). -/
def dcSearchedLength (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : ℝ :=
  let m := dcSlideMethod memory estimate
  lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k)

/-- The source's actual physical fresh defect pairing for one retained old step.
Use: retain the true finite operator variation inside the linearized residual sum.
Article: main_krylov, thm:dcs(c), D_ij. -/
def dcFreshPairing (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (i j : ℕ) : ℝ :=
  let m := dcSlideMethod memory estimate
  inner ℝ (probedStep m A B g i) ((A j-A i) (probedStep m A B g j))

/-- The actual DC-slide residual has precisely the original chronological
frozen-reference-estimate product expansion, with one common quadratic bound
over every compact set of genuine positive nonstagnating references.
Use: closes the source C-one compact-uniform linearization without assumed
trajectory regularity, inverse domains, response derivatives or remainder fields. With freezeSearch=true the real
searched lengths are frozen too, yielding the reference-weight expansion.
Article: main_krylov, thm:dcs(c), full compact-uniform O(omega squared) formula.
Proof: primitive observed coefficient charts derive actual step, search and
chosen-estimate C-one regularity. Genuine quadratic histories make every real
fresh defect zero and every retained reference cross-Gram positive. Actual
smooth observation charts preserve all true inverse domains on one compact
tube. On that tube the exact native residual product identity applies; the
proved compact C-one zero-product estimate freezes only the real estimates. -/
theorem dc_slide_compact_residual_expansion
    (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k) (estimate : History E → ℝ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (Q : X → E →L[ℝ] E)
    (T i N : ℕ) (hT : i+N<T) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K,∀ k<T,ContDiffAt ℝ 1 (fun p => A p k) x)
    (hB : ∀ x∈K,∀ k<T,ContDiffAt ℝ 1 (fun p => B p k) x)
    (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hAx : ∀ x∈K,A x=fun _ => Q x) (hBx : ∀ x∈K,B x=fun _ => Q x)
    (hQ : ∀ x∈K,(Q x).toLinearMap.IsSymmetric)
    (hpos : ∀ x∈K,∀ v : E,v≠0 → 0 < inner ℝ v (Q x v))
    (hpre : ∀ x∈K,∀ k<T,CG.gradient (Q x) (g x) k≠0)
    (ha : ∀ x∈K,∀ k<T,
      let H := methodRun (dcSlideMethod memory estimate) (fun _ => Q x) (fun _ => Q x) (g x) k
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,∀ k<T,0<estimate (methodRun (dcSlideMethod memory estimate)
      (fun _ => Q x) (fun _ => Q x) (g x) k))
    (hAi : ∀ p : X,(A p i).toLinearMap.IsSymmetric)
    (hkeep : ∀ j<N,(i+1+j)-1-i<memory (i+1+j)) (freezeSearch : Bool := false) :
    let m := dcSlideMethod memory estimate
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤δ →
      ‖inner ℝ (probedStep m (A y) (B y) (g y) i) (probedGradient m (A y) (B y) (g y) (i+1+N))-
        ∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,
          (1-(if freezeSearch then dcSearchedLength memory estimate (A x) (B x) (g x) (i+1+l)
            else dcSearchedLength memory estimate (A y) (B y) (g y) (i+1+l))/
            estimate (methodRun m (A x) (B x) (g x) (i+1+l))))*
          dcFreshPairing memory estimate (A y) (B y) (g y) i (i+1+j)‖≤C*‖y-x‖^2 := by
  let m := dcSlideMethod memory estimate
  have hsmooth (x : X) (hx : x∈K) := dc_slide_smoothCycleAt memory hm estimate (Q x) (hQ x hx)
    (hpos x hx) (g x) T (hpre x hx) 1 (ha x hx) (ha0 x hx)
  have hstep (x : X) (hx : x∈K) (k : ℕ) (hk : k<T) :
      ContDiffAt ℝ 1 (fun p => probedStep m (A p) (B p) (g p) k) x :=
    (smoothProbed_fields_regular m (dc_slide_consistent memory hm estimate) A B g x T
      (hA x hx) (hB x hx) (hg x hx) (Q x) (hAx x hx) (hBx x hx) (hQ x hx) (hpos x hx)
      (hpre x hx) (hsmooth x hx) k hk).2.2.1
  have hsearch (x : X) (hx : x∈K) (k : ℕ) (hk : k<T) :
      ContDiffAt ℝ 1 (fun p => dcSearchedLength memory estimate (A p) (B p) (g p) k) x :=
    (smoothProbed_search_regular m (dc_slide_consistent memory hm estimate) A B g x T
      (hA x hx) (hB x hx) (hg x hx) (Q x) (hAx x hx) (hBx x hx) (hQ x hx) (hpos x hx)
      (hpre x hx) (hsmooth x hx) k hk).1
  let alpha := fun p k => dcSearchedLength memory estimate (A p) (B p) (g p) (i+1+k)
  let a := fun p k => estimate (methodRun m (A p) (B p) (g p) (i+1+k))
  let d := fun p j => dcFreshPairing memory estimate (A p) (B p) (g p) i (i+1+j)
  have hd : ∀ x∈K,∀ j<N,ContDiffAt ℝ 1 (fun y => d y j) x := by
    intro x hx j hj
    exact (hstep x hx i (by omega)).inner ℝ
      (((hA x hx (i+1+j) (by omega)).sub (hA x hx i (by omega))).clm_apply
        (hstep x hx (i+1+j) (by omega)))
  have hd0 : ∀ x∈K,∀ j<N,d x j=0 := by
    intro x hx j _
    dsimp only [d,dcFreshPairing]
    rw [hAx x hx,sub_self,_root_.zero_apply,inner_zero_right]
  have haC : ∀ x∈K,∀ l<N,ContDiffAt ℝ 1 (fun p => a p l) x := by
    intro x hx l hl
    exact dc_slide_estimate_contDiffAt memory hm estimate A B g x T (hA x hx) (hB x hx) (hg x hx)
      (Q x) (hAx x hx) (hBx x hx) (hQ x hx) (hpos x hx) (hpre x hx) (ha x hx) (ha0 x hx) (i+1+l) (by omega)
  have haNZ : ∀ x∈K,∀ l<N,a x l≠0 := by
    intro x hx l hl
    dsimp only [a]
    rw [hAx x hx,hBx x hx]
    exact (ha0 x hx (i+1+l) (by omega)).ne'
  obtain ⟨δ0,C,hδ0,hC,hbound⟩ := compact_frozen_residual_products alpha a d N K hK
    (fun x hx l hl => hsearch x hx (i+1+l) (by omega)) haC haNZ hd hd0 (freezeSearch := freezeSearch)
  let D : Set X := {p | ∀ j : Fin N,IsUnit (crossGram
    (windowImages (selectedWindow memory (methodRun m (A p) (B p) (g p) (i+1+j.val))))
    (windowSteps (selectedWindow memory (methodRun m (A p) (B p) (g p) (i+1+j.val))))).det}
  have hKD : K⊆interior D := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.eventually_all.mpr
    intro j
    let k := i+1+j.val
    have hk : k<T := by dsimp only [k];omega
    have ht := smoothProbed_trace_regular m (dc_slide_consistent memory hm estimate) A B g x k
      (fun l hl => hA x hx l (hl.trans hk)) (fun l hl => hB x hx l (hl.trans hk)) (hg x hx)
      (Q x) (hAx x hx) (hBx x hx) (hQ x hx) (hpos x hx)
      (fun l hl => hpre x hx l (hl.trans hk)) ((hsmooth x hx).mono m hk.le)
    have hshape : ∀ᶠ p in 𝓝 x,(methodRun m (A p) (B p) (g p) k).queryShape=
        (methodRun m (A x) (B x) (g x) k).queryShape :=
      Eventually.of_forall fun p =>
        (methodRun_empty_corrections_shape m (fun _ _ => rfl) (A p) (B p) (g p) k).trans
          (methodRun_empty_corrections_shape m (fun _ _ => rfl) (A x) (B x) (g x) k).symm
    apply observed_window_domain_eventually memory _ x ht hshape
    have hW : selectedWindow memory (methodRun m (A x) (B x) (g x) k)=
        (referencePairs (Q x) (g x) k).take (memory k) := by
      dsimp only [m]
      rw [hAx x hx,hBx x hx,dc_slide_reference_run memory hm estimate (Q x) (hQ x hx) (hpos x hx) (g x) k]
      unfold selectedWindow
      rw [methodRun_length,(fcMethod_static memory (Q x) (hQ x hx) (hpos x hx) (g x) (fun l _ => hm l) k).2]
    rw [hW]
    exact (retainedConjugacy_posDef (Q x) (hQ x hx) (hpos x hx) (g x) k (memory k)
      (fun l hl => hpre x hx l (hl.trans hk))).det_pos.ne'
  obtain ⟨δD,hδD,hDtube⟩ := hK.exists_cthickening_subset_open isOpen_interior hKD
  refine ⟨min δ0 δD,C,lt_min hδ0 hδD,hC,?_⟩
  intro x hx y hy
  have hDy : y∈D := interior_subset (hDtube (mem_cthickening_of_dist_le y x δD K hx
    (by simpa only [dist_eq_norm] using hy.trans (min_le_right _ _))))
  have he := dc_slide_residual_products memory estimate (A y) (B y) (g y) i N (hAi y) hkeep
    (fun j hj => hDy ⟨j,hj⟩)
  have hexact : inner ℝ (probedStep m (A y) (B y) (g y) i) (probedGradient m (A y) (B y) (g y) (i+1+N))=
      ∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,(1-alpha y l/a y l))*d y j := he
  rw [hexact]
  exact hbound x hx y (hy.trans (min_le_left _ _))

end
end krylov.Cancellation
