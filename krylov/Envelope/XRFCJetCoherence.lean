import krylov.Envelope.XRFCBlockJets
import krylov.Envelope.GradientJetLift
import krylov.Envelope.ScalarJets
import krylov.Envelope.KrylovFlags
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual full XRFC virtual-step filtration.
Use: derive the genuine virtual-step first-jet coherence from primitive C-two trial charts and original actual quadratic CG domains.
Source: actual XRFC reference solves and regularity, native stored-step solve jet closure and true reference-gradient coordinate lifts.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every genuinely executed full-memory XRFC virtual step has the true measured-CG gradient-lift first-jet coherence under primitive smooth trial rules.
Use: Every genuinely executed full-memory XRFC virtual step has the true measured-CG gradient-lift first-jet coherence under primitive smooth trial rules.
Article: main_krylov, thm:E1, actual full XRFC virtual-step filtration.
Proof: Induct through actual evaluated steps using the genuine correction and effective-gradient direction solves. Both consecutive real corrections preserve the actual current jet flag, so their true virtual step does too; identify its actual CG reference and restrict the genuine coordinate lift. -/
theorem xrfc_virtual_step_jet_coherence (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (g : E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (hA0 : A 0=fun _ => Q)
    (N : ℕ) (hA : ∀ i,ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hpre : ∀ i≤N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A 0) g k)) :
    let dg := fun k => deriv (fun t => xrfcVirtualGradient trial (A t) g k) 0
    ∀ k<N,deriv (fun t => xrfcVirtualStep trial (A t) g k) 0-
      gradientJetLift Q g dg k (referenceStep Q g k)∈CG.krylovSpace Q g (k+1) := by
  dsimp only
  let m := xrfcMethod fullMemory trial (E := E)
  let H := fun k t => oneGradientRun m (A t) g k
  let s := fun k t => oneGradientStep m (A t) g k
  let c := fun k t => m.output (H k t)
  let G := fun k t => xrfcVirtualGradient trial (A t) g k
  let dg := fun k => deriv (G k) 0
  let L := gradientJetLift Q g dg N
  let J := fun k => jetSubspace (CG.krylovSpace Q g (k+1)) L
  -- Primitive trial charts and real reference model positivity derive regularity of every actual queried and virtual field.
  have hreg := quadraticXRFC_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
    Q hA0 hQ hpos N (fun i hi => hpre i hi.le) ht hT
  have hdom (k : ℕ) (hk : k≤N) := xrfc_full_array_domains trial Q hQ hpos g N (fun i hi => hpre i hi.le) ht k hk
  have hb (k : ℕ) (hk : k≤N) := oneGradient_virtualBlock_contDiffAt m A (fun _ => g) 0 k
    (fun i _ => hA i) (fun i hi => hreg.2 i (hi.trans_le hk)) (hreg.1 k hk)
    (by rw [hA0];exact (hdom k hk).2) (by rw [hA0];exact (hdom k hk).1)
  have hC (k : ℕ) (hk : k≤N) : ContDiffAt ℝ 2 (c k) 0 := (hb k hk).1
  have hG (k : ℕ) (hk : k≤N) : ContDiffAt ℝ 2 (G k) 0 := (hb k hk).2.1
  have hD (k : ℕ) (hk : k≤N) : ContDiffAt ℝ 2
      (fun t => windowDirection (selectedWindow fullMemory (H k t)) (G k t)) 0 := (hb k hk).2.2
  have hline (i : ℕ) (hi : i≤N) : CG.length Q g i≠0 :=
    (CG.invariant_line_pos Q hpos g i (CG.invariant Q hQ hpos g i (fun j hj => hpre j (by omega))) (hpre i hi)).2.1.ne'
  have hGref (k : ℕ) (hk : k≤N) : G k 0=CG.gradient Q g k := by
    dsimp only [G,xrfcVirtualGradient,oneGradientGradient]
    rw [hA0,selectedWindow_full]
    exact (xrfc_full_reference trial Q hQ hpos g N (fun i hi => hpre i hi.le) ht k hk).2.1
  have hGj (k : ℕ) (hk : k≤N) : (G k 0,deriv (G k) 0)∈J k := by
    rw [hGref k hk]
    constructor
    · rw [CG.krylovSpace_eq_span_gradients Q g (k+1) (fun i hi => hline i (by omega))]
      exact Submodule.subset_span ⟨k,Nat.lt_succ_self k,rfl⟩
    · change dg k-L (CG.gradient Q g k)∈_
      rw [gradientJetLift_gradient Q hQ hpos g dg N hpre k hk,sub_self]
      exact Submodule.zero_mem _
  have hmono {i j : ℕ} (hij : i≤j) : J i≤J j :=
    jetSubspace_mono (krylovSpace_mono Q g (by omega)) (fun _ _ => rfl)
  have hblock (k : ℕ) (hk : k≤N) (V : Submodule ℝ E)
      (hj : ∀ i<k,(s i 0,deriv (s i) 0)∈jetSubspace V L) :=
    xrfc_virtual_block_jet trial A g k V L (fun i _ => (hA i).of_le (by norm_num))
      (fun i hi => (hreg.2 i (hi.trans_le hk)).of_le (by norm_num))
      ((hreg.1 k hk).of_le (by norm_num))
      (by rw [hA0];exact (hdom k hk).2) (by rw [hA0];exact (hdom k hk).1) hj
  -- Actual stored-step jets close recursively through the true model correction and the effective-gradient direction.
  have hsj (k : ℕ) (hk : k<N) : (s k 0,deriv (s k) 0)∈J k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hj (i : ℕ) (hi : i<k) : (s i 0,deriv (s i) 0)∈J k := hmono hi.le (ih i hi (hi.trans hk))
      have hc := (hblock k hk.le (CG.krylovSpace Q g (k+1)) hj).1
      have hd := (hblock k hk.le (CG.krylovSpace Q g (k+1)) hj).2 (hGj k hk.le)
      have htr := actual_trial_contDiffAt trial m A (fun _ => g) 0 k contDiffAt_const
        (fun i hi => hreg.2 i (hi.trans hk)) (fun i hi => hreg.1 i (hi.trans hk.le)) (hT k hk)
      have hdif := (htr.differentiableAt (by norm_num)).hasDerivAt.smul
        ((hD k hk.le).differentiableAt (by norm_num)).hasDerivAt
      have hsum := ((hC k hk.le).differentiableAt (by norm_num)).hasDerivAt.add hdif
      change HasDerivAt (s k) _ 0 at hsum
      rw [hsum.deriv]
      exact (J k).add_mem hc (jetSubspace_smul _ L hd _ _)
  -- The actual virtual step adds its true next correction and subtracts its true preceding correction in the same jet flag.
  intro k hk
  let V := CG.krylovSpace Q g (k+1)
  have hc := (hblock k hk.le V (fun i hi => hmono hi.le (hsj i (hi.trans hk)))).1
  have hcn := (hblock (k+1) (by omega) V (fun i hi => hmono (by omega) (hsj i (by omega)))).1
  have hpair := (J k).sub_mem ((J k).add_mem (hsj k hk) hcn) hc
  have hdif := (((hreg.2 k hk).differentiableAt (by norm_num)).hasDerivAt.add
    ((hC (k+1) (by omega)).differentiableAt (by norm_num)).hasDerivAt).sub
    ((hC k hk.le).differentiableAt (by norm_num)).hasDerivAt
  have he : (fun t => xrfcVirtualStep trial (A t) g k)=(fun t => s k t+c (k+1) t-c k t) := by
    funext t
    exact xrfcVirtualStep_corrections trial (A t) g k
  have hdr : deriv (fun t => xrfcVirtualStep trial (A t) g k) 0=deriv (s k) 0+deriv (c (k+1)) 0-deriv (c k) 0 := by
    rw [he]
    exact hdif.deriv
  -- Identify the genuine CG virtual reference before restricting the actual gradient-coordinate lift.
  have href : xrfcVirtualStep trial (A 0) g k=referenceStep Q g k := by
    dsimp only [xrfcVirtualStep,xrfcVirtualPoint]
    rw [hA0,(xrfc_full_reference trial Q hQ hpos g N (fun i hi => hpre i hi.le) ht (k+1) (by omega)).1,
      (xrfc_full_reference trial Q hQ hpos g N (fun i hi => hpre i hi.le) ht k hk.le).1,CG.displacement_succ]
    exact add_sub_cancel_left _ _
  have href' : s k 0+c (k+1) 0-c k 0=referenceStep Q g k := by rw [← href];exact (congrFun he 0).symm
  have hh : deriv (fun t => xrfcVirtualStep trial (A t) g k) 0-L (referenceStep Q g k)∈V := by
    have hp := hpair.2
    change deriv (s k) 0+deriv (c (k+1)) 0-deriv (c k) 0-L (s k 0+c (k+1) 0-c k 0)∈V at hp
    rwa [href',← hdr] at hp
  have hstepK : referenceStep Q g k∈CG.krylovSpace Q g (k+1) :=
    Submodule.smul_mem _ _ (cgDirection_mem_krylov Q g k (fun i hi => hline i (by omega)))
  rwa [gradientJetLift_restrict Q hQ hpos g dg N k hpre hk.le hstepK] at hh
end
end krylov.Envelope
