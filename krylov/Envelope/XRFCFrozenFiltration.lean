import krylov.Envelope.XRFCJetCoherence
import krylov.Envelope.FrozenFiltration
import krylov.Envelope.InjectionDifferences
import krylov.Methods.VirtualBalance
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine full virtual frozen-response theorem.
Use: derive the actual XRFC virtual-point and effective-gradient first variations modulo the true Krylov flag, driven by the genuine differentiated executed injection sum.
Source: exact real virtual affine balance, primitive C-two XRFC regularity, actual virtual-step jet coherence and the proved measured-CG frozen filtered induction.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine first derivative of the actually executed XRFC effective-gradient injection sum.
Use: The genuine first derivative of the actually executed XRFC effective-gradient injection sum.
Article: main_krylov, thm:E1, genuine full virtual frozen-response theorem.
Proof: Differentiate the true computed chronological operator-defect sum at the actual quadratic reference. -/
def xrfcInjectionJet (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  deriv (fun t => virtualInjectionSum (xrfcMethod fullMemory trial) (A t) Q g k) 0

/-- The actual full-memory XRFC virtual displacement and effective-gradient derivatives have the genuine measured-CG frozen response modulo their true physical Krylov flags.
Use: The actual full-memory XRFC virtual displacement and effective-gradient derivatives have the genuine measured-CG frozen response modulo their true physical Krylov flags.
Article: main_krylov, thm:E1, genuine full virtual frozen-response theorem.
Proof: Differentiate the exact actual virtual affine balance and genuine virtual displacement sum. Actual step coherence and chronological injection telescoping supply the proved filtered frozen induction, with all real domains derived from primitive trial rules. -/
theorem xrfc_frozen_filtration (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (g : E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (hA0 : A 0=fun _ => Q)
    (N : ℕ) (hA : ∀ i,ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hpre : ∀ i≤N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A 0) g k)) :
    let zeta := injectionDifference (xrfcInjectionJet trial A Q g)
    ∀ k≤N,
      (deriv (fun t => xrfcVirtualPoint trial (A t) g k) 0-
        frozenDisplacement Q (CG.length Q g) (CG.beta Q g) zeta k∈CG.krylovSpace Q g k) ∧
      (deriv (fun t => xrfcVirtualGradient trial (A t) g k) 0-
        frozenResponse Q (CG.length Q g) (CG.beta Q g) zeta k 0∈(CG.krylovSpace Q g k).map Q.toLinearMap) := by
  dsimp only
  let m := xrfcMethod fullMemory trial (E := E)
  let X := fun k t => xrfcVirtualPoint trial (A t) g k
  let G := fun k t => xrfcVirtualGradient trial (A t) g k
  let J := fun k t => virtualInjectionSum m (A t) Q g k
  let dJ := xrfcInjectionJet trial A Q g
  let zeta := injectionDifference dJ
  let ds := fun k => deriv (fun t => xrfcVirtualStep trial (A t) g k) 0
  let dg := fun k => deriv (G k) 0
  -- Derive genuine actual output and effective-gradient regularity from primitive trial charts and positive reference models.
  have hx (k : ℕ) (hk : k≤N) : ContDiffAt ℝ 2 (X k) 0 :=
    (quadraticXRFC_output_contDiffAt trial A (fun _ => Q) (fun _ => g) 0 hA contDiffAt_const contDiffAt_const
      Q hA0 hQ hpos k (fun i hi => hpre i (by omega)) (fun i hi => ht i (by omega))
      (fun i hi => hT i (by omega))).1
  have hreg := quadraticXRFC_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
    Q hA0 hQ hpos N (fun i hi => hpre i hi.le) ht hT
  have hg (k : ℕ) (hk : k≤N) : ContDiffAt ℝ 2 (G k) 0 := by
    have hd := xrfc_full_array_domains trial Q hQ hpos g N (fun i hi => hpre i hi.le) ht k hk
    exact (oneGradient_virtualBlock_contDiffAt m A (fun _ => g) 0 k (fun i _ => hA i)
      (fun i hi => hreg.2 i (hi.trans_le hk)) (hreg.1 k hk)
      (by rw [hA0];exact hd.2) (by rw [hA0];exact hd.1)).2.1
  have he (k : ℕ) (t : ℝ) : J k t=G k t-g-Q (X k t) := by
    have h := xrfc_virtual_gradient_balance trial (A t) Q g k
    change G k t=g+Q (X k t)+J k t at h
    rw [h]
    abel
  -- Differentiate the exact executed affine balance, without inserting a presumed virtual trajectory expansion.
  have hdJ (k : ℕ) (hk : k≤N) : dJ k=dg k-Q (deriv (X k) 0) := by
    have hh := (((hg k hk).differentiableAt (by norm_num)).hasDerivAt.sub_const g).sub
      (Q.hasFDerivAt.comp_hasDerivAt 0 ((hx k hk).differentiableAt (by norm_num)).hasDerivAt)
    have hactual : HasDerivAt (J k) (dg k-Q (deriv (X k) 0)) 0 :=
      hh.congr_of_eventuallyEq (Eventually.of_forall fun t => he k t)
    exact hactual.deriv
  have h0 : dJ 0=0 := by
    have heq : J 0=(fun _ : ℝ => (0 : E)) := by funext t;simp [J,virtualInjectionSum]
    change deriv (J 0) 0=0
    rw [heq,deriv_const]
  -- The real virtual point is the actual finite sum of its genuine consecutive virtual steps.
  have hdx (k : ℕ) (hk : k≤N) : deriv (X k) 0=∑ i∈Finset.range k,ds i := by
    have hs (i : ℕ) (hi : i<k) : HasDerivAt (fun t => xrfcVirtualStep trial (A t) g i) (ds i) 0 :=
      (((hx (i+1) (by omega)).differentiableAt (by norm_num)).hasDerivAt.sub
        ((hx i (by omega)).differentiableAt (by norm_num)).hasDerivAt).differentiableAt.hasDerivAt
    have hsum := HasDerivAt.sum (fun i (hi : i∈Finset.range k) => hs i (Finset.mem_range.mp hi))
    have heq : X k=(fun t => ∑ i∈Finset.range k,xrfcVirtualStep trial (A t) g i) := by
      funext t
      exact xrfcVirtualPoint_sum trial (A t) g k
    rw [heq]
    have hf : (fun t => ∑ i∈Finset.range k,xrfcVirtualStep trial (A t) g i)=
        ∑ i∈Finset.range k,(fun t => xrfcVirtualStep trial (A t) g i) := by
      funext t
      simp only [Finset.sum_apply]
    rw [hf]
    exact hsum.deriv
  have hbal (k : ℕ) (hk : k≤N) : dg k=Q (∑ i∈Finset.range k,ds i)+∑ i∈Finset.range k,zeta (i+1) := by
    rw [injectionDifference_sum dJ h0,hdJ k hk,hdx k hk]
    abel
  -- The actual differentiated balance and proved virtual-step coherence now drive the genuine frozen induction.
  have hfil := coherent_steps_frozen_filtration Q hQ hpos g N (fun i hi => hpre i hi.le) ds dg zeta hbal
    (xrfc_virtual_step_jet_coherence trial A g Q hQ hpos hA0 N hA hpre ht hT)
  intro k hk
  refine ⟨?_,?_⟩
  · rw [hdx k hk]
    exact hfil k hk
  · have hf := frozen_gradient_displacement Q (CG.length Q g) (CG.beta Q g) zeta k
    change dg k-_∈_
    rw [hbal k hk,hf]
    have hh : Q (∑ i∈Finset.range k,ds i)+(∑ i∈Finset.range k,zeta (i+1))-
        (Q (frozenDisplacement Q (CG.length Q g) (CG.beta Q g) zeta k)+(∑ i∈Finset.range k,zeta (i+1)))=
        Q ((∑ i∈Finset.range k,ds i)-frozenDisplacement Q (CG.length Q g) (CG.beta Q g) zeta k) := by rw [map_sub];abel
    rw [hh]
    exact Submodule.mem_map_of_mem (hfil k hk)
end
end krylov.Envelope
