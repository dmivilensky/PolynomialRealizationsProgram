import krylov.Correction.RFCSDomains
import krylov.Methods.RFCSHomogeneous

/-!
Article: main_krylov, thm:RFCS, genuine physical inverse and gate domains.
Use: Transfer the compact normalized source domains to the actual cycle
scale and its original observed list matrices, including the empty old window.
Source: proved exact RFC-S homogeneity, genuine retained-age coordinates,
determinant scaling and the original measured defect gate.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The actual direct-source observed defect has exactly its finite retained-age spectral norm.
Use: Transport genuine observed gate acceptance between normalized and physical cycle scales.
Article: main_krylov, thm:RFCS, actual physical domains.
Proof: The true complete pair transcript identifies the retained list; the proved coordinate bridge preserves its spectral norm. -/
theorem rfcs_direct_window_norm (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) :
    ‖windowDefect (selectedWindow fullMemory (rfcSRun fullMemory (rfcsDirectProbe base z)
      (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i))‖=
      ‖pairDefect (rfcsDirectOldSteps base i z) (rfcsDirectOldImages base i z)‖ := by
  let s := rfcSStep fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1
  let y := rfcSSecant fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1
  rw [selectedWindow_of_executed_pairs fullMemory _ s y i (rfcSRun_pairs _ _ _ _ _ _)]
  have hc := retainedWindow_coordinates s y i (fullMemory i)
  exact windowDefect_norm_of_coordinates _ _ _ _ hc.1 hc.2

/-- Every positive full-memory direct-source iteration has a genuinely nonempty retained window.
Use: Justify the actual correction branch without an assumed nonempty-history premise.
Article: main_krylov, thm:RFCS, actual physical domains.
Proof: Its actual retained length is the positive iteration index. -/
theorem rfcs_direct_window_nonempty (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ) (hi : 0 < i)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) :
    selectedWindow fullMemory (rfcSRun fullMemory (rfcsDirectProbe base z)
      (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i)≠[] := by
  intro he
  have hl := congrArg List.length he
  rw [selectedWindow_of_executed_pairs fullMemory _ _ _ i (rfcSRun_pairs _ _ _ _ _ _),
    List.length_take,executedPairs_length,fullMemory,Nat.min_self,List.length_nil] at hl
  exact hi.ne' hl

set_option maxHeartbeats 800000 in
/-- Every nonzero common initial-gradient scale preserves the actual source inverse, positive-curvature and observed-gate domains.
Use: Apply compact normalized source domains to the genuine physical nonlinear cycle.
Article: main_krylov, thm:RFCS, actual physical domains.
Proof: Exact RFC-S homogeneity scales the real old steps, secants, direction and probe. Both solve determinants acquire a nonzero even-degree factor; curvature acquires the positive square factor and the observed defect is unchanged. -/
theorem rfcs_direct_domain_scalar (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ : RFCSOperatorParameters (k+1)) (c : ℝ) (hc : c≠0)
    (i : ℕ) (hdom : rfcsDirectIterationDomain base i (g,Θ)) :
    rfcsDirectIterationDomain base i (c • g,Θ) := by
  let S := rfcsDirectOldSteps base i (g,Θ)
  let Y := rfcsDirectOldImages base i (g,Θ)
  let Ap := rfcsDirectProbe base (g,Θ)
  let A := rfcsDirectLine base (g,Θ)
  let d := rfcSDirection fullMemory Ap A A g i
  let p := Ap i d
  have hs : rfcsDirectOldSteps base i (c • g,Θ)=(fun j => c • S j) := by
    funext j
    have hj := j.isLt
    change rfcSStep fullMemory Ap A A (c • g) (i-1-j.val)=c • rfcSStep fullMemory Ap A A g (i-1-j.val)
    exact ((rfcS_scalar fullMemory Ap A A g c hc i).2 _ (by omega)).2.2.1
  have hy : rfcsDirectOldImages base i (c • g,Θ)=(fun j => c • Y j) := by
    funext j
    have hj := j.isLt
    change rfcSSecant fullMemory Ap A A (c • g) (i-1-j.val)=c • rfcSSecant fullMemory Ap A A g (i-1-j.val)
    exact ((rfcS_scalar fullMemory Ap A A g c hc i).2 _ (by omega)).2.2.2
  have hd : rfcSDirection fullMemory (rfcsDirectProbe base (c • g,Θ))
      (rfcsDirectLine base (c • g,Θ)) (rfcsDirectLine base (c • g,Θ)) (c • g) i=c • d :=
    ((rfcS_scalar fullMemory Ap A A g c hc (i+1)).2 i (Nat.lt_succ_self i)).1
  have hU : (Fin.cons (c • d) (fun j => c • S j) : Fin (min (fullMemory i) i+1) → _)=
      fun j => c • (Fin.cons d S : Fin (min (fullMemory i) i+1) → _) j := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have hZ : (Fin.cons (c • p) (fun j => c • Y j) : Fin (min (fullMemory i) i+1) → _)=
      fun j => c • (Fin.cons p Y : Fin (min (fullMemory i) i+1) → _) j := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  obtain ⟨hC,hM,hcurv,hgate⟩ := hdom
  change (crossGram Y S).det≠0 at hC
  change (pairModel (Fin.cons d S) (Fin.cons p Y)).det≠0 at hM
  change 0 < inner ℝ d p at hcurv
  unfold rfcsDirectIterationDomain
  dsimp only
  have hpOp : rfcsDirectProbe base (c • g,Θ)=Ap := rfl
  rw [hs,hy,hd,hpOp,map_smul]
  refine ⟨?_,?_,?_,?_⟩
  · rw [crossGram_scalar,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hc hc)) hC
  · rw [hU,hZ,pairModel_scalar,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hc hc)) hM
  · have hh := mul_pos (mul_self_pos.mpr hc) hcurv
    simpa only [real_inner_smul_left,real_inner_smul_right,mul_assoc] using hh
  · intro hi
    refine ⟨rfcs_direct_window_nonempty base i hi (c • g,Θ),?_⟩
    change ‖windowDefect (selectedWindow fullMemory (rfcSRun fullMemory
      (rfcsDirectProbe base (c • g,Θ)) (rfcsDirectLine base (c • g,Θ))
      (rfcsDirectLine base (c • g,Θ)) (c • g) i))‖<1
    rw [rfcs_direct_window_norm base i (c • g,Θ),hs,hy,pairDefect_scalar S Y c hc]
    rw [← rfcs_direct_window_norm base i (g,Θ)]
    exact (hgate hi).2

/-- The actual old conjugacy inverse, augmented latest-model inverse, positive probe curvature and nonempty observed defect gate.
Use: State physical nonlinear well-definedness directly in the real measured list coordinates.
Article: main_krylov, thm:RFCS, actual physical domains. -/
def observedCorrectionDomain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : List (E × E)) (d p : E) : Prop :=
  (crossGram (windowImages W) (windowSteps W)).det≠0 ∧
    (windowModel ((d,p)::W)).det≠0 ∧ 0 < inner ℝ d p ∧
    (W≠[] → ‖windowDefect W‖<1)

/-- Genuine direct-source domains imply the domains of the original observed list matrices and true measured probe.
Use: Transfer source regularity to actual physical nonlinear solves and gates.
Article: main_krylov, thm:RFCS, actual physical domains.
Proof: Exact retained and augmented coordinates identify both genuine determinants through the same finite index equivalence. A nonempty full-memory window forces a positive iteration index, where the proved actual gate applies. -/
theorem rfcs_direct_domain_observed (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (i : ℕ) (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1))
    (hdom : rfcsDirectIterationDomain base i z) :
    observedCorrectionDomain (selectedWindow fullMemory
      (rfcSRun fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i))
      (rfcSDirection fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i)
      (rfcsDirectProbe base z i
        (rfcSDirection fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i)) := by
  let s := rfcSStep fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1
  let y := rfcSSecant fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1
  let d := rfcSDirection fullMemory (rfcsDirectProbe base z) (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i
  let p := rfcsDirectProbe base z i d
  have hw := selectedWindow_of_executed_pairs fullMemory _ s y i (rfcSRun_pairs _ _ _ _ _ _)
  obtain ⟨hC,hM,hcurv,hgate⟩ := hdom
  refine ⟨?_,?_,hcurv,?_⟩
  · rw [hw,crossGram_det_of_coordinates _ _ _ _
      (retainedWindow_coordinates s y i (fullMemory i)).1
      (retainedWindow_coordinates s y i (fullMemory i)).2]
    exact hC
  · rw [hw,windowModel_of_coordinates _ _ _ _
      (augmentedWindow_coordinates s y i (fullMemory i) d p).1
      (augmentedWindow_coordinates s y i (fullMemory i) d p).2,
      Matrix.det_submatrix_equiv_self]
    exact hM
  · intro hn
    have hi : 0 < i := by
      by_contra h
      have hz : i=0 := by omega
      subst i
      rw [hw] at hn
      exact hn rfl
    exact (hgate hi).2

end
end krylov.Correction
