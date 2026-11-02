import krylov.Methods.DeferredActualResidual
import krylov.Methods.DeferredPrefix
import krylov.Envelope.DeferredModelDomain
import krylov.Envelope.ZeroOperatorPairJet
import krylov.Variation.FCResponse
import krylov.Reference.EnergyPositive

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual calibrated deferred residual first variation.
Use: prove genuine final deferred old-step residual derivatives depend
only on the actual fresh chronological segment defect on true CG steps.
Source: actual primitive smooth deferred membership and real model domains,
true recorded residual transfer and genuine zero-reference product derivatives.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Filter Topology
variable {n : ℕ}

/-- With the true last reference line length supplied, every actual calibrated deferred old-step residual derivative equals exactly its genuine fresh cumulative-defect pairing on the real CG steps.
Use: With the true last reference line length supplied, every actual calibrated deferred old-step residual derivative equals exactly its genuine fresh cumulative-defect pairing on the real CG steps.
Article: main_krylov, apB:lem:mu(d), actual calibrated deferred residual first variation.
Proof: Derive actual fields and search C-two regularity from true primitive source membership. The genuine old residual and real inverse-estimate damping both vanish at the true reference, annihilating their product derivative. The real zero-reference segment mismatch removes both actual step-derivative terms. Transfer the exact genuine residual identity on its proved actual inverse neighborhood. -/
theorem deferred_residual_derivative (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hB : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => B t i) 0) (hB0 : B 0=fun _ => cgOperator base)
    (hcount : k+1≤referenceAtomCount base hb g) (i : ℕ) (hi : i<k) :
    let A := canonicalFCPath base E
    let a := CG.length (cgOperator base) g k
    let m := deferredMethod fullMemory (k+1) a
    deriv (fun t => inner ℝ (probedStep m (A t) (B t) g i)
      (probedGradient m (A t) (B t) g (k+1))) 0=
    inner ℝ (referenceStep (cgOperator base) g i)
      ((cumulativeDrift base E k-cumulativeDrift base E i) (referenceStep (cgOperator base) g k)) := by
  -- Derive every genuine executed field and actual reference domain from the true primitive deferred source class.
  let Q := cgOperator base
  let a := CG.length Q g k
  let M := smoothDeferredClass fullMemory (fun _ hk => hk) (k+1) a (E := EuclideanSpace ℝ (Fin n))
  let m := M.policy
  let A := canonicalFCPath base E
  let S := fun j t => probedStep m (A t) (B t) g j
  let G := fun j t => probedGradient m (A t) (B t) g j
  let α := fun t => lineLength (G k t) (probedDirection m (A t) (B t) g k) (probedProbe m (A t) (B t) g k)
  have hQ := cgOperator_positive base hb
  have hpre (j : ℕ) (hj : j<k+1) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j (hj.trans_le hcount)
  have hs := M.smooth Q hQ.1 hQ.2 g (k+1) hpre
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun t => A t j) 0 := (canonicalFCPath_calculus base E j).1.contDiffAt
  have hA0 : A 0=fun _ => Q := canonicalFCPath_zero base E
  have hfields (j : ℕ) (hj : j<k+1) := smoothProbed_fields_regular m M.consistent A B (fun _ => g) 0 (k+1)
    (fun j _ => hA j) hB contDiffAt_const Q hA0 hB0 hQ.1 hQ.2 hpre hs j hj
  have hSi : ContDiffAt ℝ 2 (S i) 0 := (hfields i (by omega)).2.2.1
  have hSk : ContDiffAt ℝ 2 (S k) 0 := (hfields k (by omega)).2.2.1
  have hGk : ContDiffAt ℝ 2 (G k) 0 := smoothProbed_gradient_regular m M.consistent A B (fun _ => g) 0 k
    (fun j _ => hA j) (fun j hj => hB j (by omega)) contDiffAt_const Q hA0 hB0 hQ.1 hQ.2
    (fun j hj => hpre j (by omega)) (hs.mono m (by omega))
  have hα : ContDiffAt ℝ 2 α 0 := (smoothProbed_search_regular m M.consistent A B (fun _ => g) 0 (k+1)
    (fun j _ => hA j) hB contDiffAt_const Q hA0 hB0 hQ.1 hQ.2 hpre hs k (by omega)).1
  -- Actual global consistency identifies the real reference steps, current gradient and genuine unscaled final CG direction.
  have hS0 (j : ℕ) : S j 0=referenceStep Q g j := by
    dsimp only [S]
    rw [hA0,hB0]
    exact quadratic_probedStep_eq_cg m M.consistent Q hQ.1 hQ.2 g j
  have hG0 : G k 0=CG.gradient Q g k := by
    dsimp only [G]
    rw [hA0,hB0]
    exact quadratic_gradient_eq_cg m M.consistent Q hQ.1 hQ.2 g k
  have hd0 : probedDirection m (A 0) (B 0) g k=CG.direction Q g k := by
    rw [hA0,hB0]
    exact deferredMethod_reference_direction fullMemory (fun _ hk => hk) (k+1) a Q hQ.1 hQ.2 g k
  have hz0 : probedProbe m (A 0) (B 0) g k=Q (CG.direction Q g k) := by
    dsimp only [probedProbe]
    rw [hd0,hA0]
  have hα0 : α 0=a := by
    dsimp only [α]
    rw [hG0,hd0,hz0]
  have ha : a≠0 := (cgLength_pos base hb g k (by omega)).ne'
  have hR0 : inner ℝ (S i 0) (G k 0)=0 := by
    rw [hS0 i,hG0,referenceStep,real_inner_smul_left,(CG.invariant Q hQ.1 hQ.2 g k
      (fun j hj => hpre j (by omega))).old_direction i hi,mul_zero]
  -- Both true factors of the unresolved old-residual product vanish at the actual calibrated reference.
  have hproduct : HasDerivAt (fun t => (1-α t/a)*inner ℝ (S i t) (G k t)) 0 0 := by
    have hC : ContDiffAt ℝ 2 (fun t : ℝ => 1-α t/a) 0 := contDiffAt_const.sub (hα.div_const a)
    have hh := (hC.differentiableAt (by norm_num)).hasDerivAt.mul
      ((hSi.inner ℝ hGk).differentiableAt (by norm_num)).hasDerivAt
    convert! hh using 1
    simp only [hα0,div_self ha,sub_self,hR0,mul_zero,zero_mul,add_zero]
  -- The real zero-reference segment defect removes both genuine moving-step derivative contributions.
  have hT0 : A 0 k-A 0 i=0 := by rw [hA0,sub_self]
  have hT := (canonicalFCPath_calculus base E k).2.sub (canonicalFCPath_calculus base E i).2
  have hD := zero_operator_pair_hasDeriv (S i) (S k) (fun t => A t k-A t i)
    (deriv (S i) 0) (deriv (S k) 0) (cumulativeDrift base E k-cumulativeDrift base E i)
    (hSi.differentiableAt (by norm_num)).hasDerivAt (hSk.differentiableAt (by norm_num)).hasDerivAt hT hT0
  rw [hS0 i,hS0 k] at hD
  -- Use the actual proved inverse neighborhood when differentiating the true executed residual identity.
  have hdom := deferred_last_model_domain A B g k a (fun j => (canonicalFCPath_calculus base E j).1) Q hA0 hQ.1 hQ.2 hpre
  have heq : (fun t => inner ℝ (S i t) (G (k+1) t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => inner ℝ (S i t) ((A t k-A t i) (S k t))+(1-α t/a)*inner ℝ (S i t) (G k t)) := by
    filter_upwards [hdom] with t ht
    exact deferredMethod_last_residual a (A t) (B t) g k i hi (canonicalFCPath_symmetric base hb E hE t i) ht
  have hh := (hD.add hproduct).congr_of_eventuallyEq heq
  change deriv (fun t => inner ℝ (S i t) (G (k+1) t)) 0=
    inner ℝ (referenceStep Q g i)
      ((cumulativeDrift base E k-cumulativeDrift base E i) (referenceStep Q g k))
  simpa only [add_zero] using hh.deriv
end
end krylov.Envelope
