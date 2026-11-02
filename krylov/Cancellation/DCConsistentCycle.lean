import krylov.Cancellation.DCConsistentResidual
import krylov.Cancellation.DeferredRadauComparison
import krylov.Cancellation.DeferredResponse
import krylov.Stability.FixedBasisOrder
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), actual consistent DC-slide end-cycle expansion.
Use: reconstruct the actual full terminal canonical gradient from the real
fresh residual coordinates under only the original C-one estimate hypothesis.
Source: actual compact C-one fresh residual expansion, primitive native
trajectory regularity, genuine first-order pairing replacement and true full
CG-basis reconstruction; no output response or remainder is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set Filter Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Correction
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Consistent original C-one data estimates give the actual full-memory
exact-search DC-slide output precisely the calibrated deferred fresh response
up to a genuine quadratic remainder on every original symmetric source axis.
Use: the end-cycle gradient conclusion is derived from all actual moving step
coordinates, including the last exact-search coordinate, with no C-two
strengthening of the source estimate rule.
Article: main_krylov, apH:dcs2(b), full native C-one cycle response.
Proof: the proved native compact residual theorem leaves only each actual
fresh defect. True C-one step regularity freezes its two outer factors with
quadratic cost. The terminal gradient vanishes at the full CG reference, so
freezing the actual paired step also costs quadratic order. Exact last search
supplies its remaining zero coordinate. The genuine full independent CG
basis reconstructs the canonical vector and the proved literal deferred
coordinate identities identify its calibrated fresh coefficient. -/
theorem dc_slide_consistent_canonical_order
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB : ∀ j<k+1,ContDiffAt ℝ 1 (fun t => B t j) 0) (hB0 : B 0=fun _ => cgOperator base)
    (ha : ∀ j<k+1,
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => cgOperator base) (fun _ => cgOperator base) g j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ j<k+1,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g j))
    (hcal : ∀ j<k+1,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g j)=CG.length (cgOperator base) g j) :
    let A := canonicalFCPath base E
    let m := dcSlideMethod fullMemory estimate
    (fun t : ℝ => cgOperator (metricRoot base)⁻¹ (probedGradient m (A t) (B t) g (k+1))-
      t • deferredResponse base g k 0 E) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^2) := by
  let Q := cgOperator base
  let A := canonicalFCPath base E
  let m := dcSlideMethod fullMemory estimate
  let S := fun j t => probedStep m (A t) (B t) g j
  let G := fun t => probedGradient m (A t) (B t) g (k+1)
  let R := cgOperator (metricRoot base)⁻¹
  let L := deferredResponse base g k 0 E
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hA (j : ℕ) : ContDiffAt ℝ 1 (fun t => A t j) 0 := (canonicalFCPath_calculus base E j).1.contDiffAt
  have hA0 : A 0=fun _ => Q := canonicalFCPath_zero base E
  have hN : k+1≤referenceAtomCount base hb g := by omega
  have hpre (j : ℕ) (hj : j<k+1) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j (hj.trans_le hN)
  have hm : CGConsistent m := dc_slide_consistent fullMemory (fun _ hj => hj) estimate
  have hsmooth := dc_slide_smoothCycleAt fullMemory (fun _ hj => hj) estimate Q hQ hpos g (k+1) hpre 1 ha ha0
  have hS (j : ℕ) (hj : j<k+1) : ContDiffAt ℝ 1 (S j) 0 :=
    (smoothProbed_fields_regular m hm A B (fun _ => g) 0 (k+1) (fun j _ => hA j) hB contDiffAt_const
      Q hA0 hB0 hQ hpos hpre hsmooth j hj).2.2.1
  have hG : ContDiffAt ℝ 1 G 0 := smoothProbed_gradient_regular m hm A B (fun _ => g) 0 (k+1)
    (fun j _ => hA j) hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hsmooth
  have hS0 (j : ℕ) : S j 0=referenceStep Q g j := by
    dsimp only [S]
    rw [hA0,hB0]
    exact quadratic_probedStep_eq_cg m hm Q hQ hpos g j
  have hG0 : G 0=0 := by
    dsimp only [G]
    rw [hA0,hB0]
    exact (quadratic_gradient_eq_cg m hm Q hQ hpos g (k+1)).trans
      ((cg_stopping_iff base hb g (k+1)).mpr (by omega))
  have hfreeze (i : ℕ) (hi : i<k+1) :
      (fun t => inner ℝ (S i t) (G t)-inner ℝ (referenceStep Q g i) (G t)) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^2) := by
    simpa only [hS0 i] using frozen_terminal_pairing_order (S i) G
      ((hS i hi).differentiableAt (by norm_num)) (hG.differentiableAt (by norm_num)) hG0
  have hres (i : ℕ) (hi : i<k) :
      (fun t => inner ℝ (S i t) (G t)-dcFreshPairing fullMemory estimate (A t) (B t) g i k)
        =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^2) := by
    have hzero : ∀ x∈({0} : Set ℝ),x=0 := fun x hx => Set.mem_singleton_iff.mp hx
    obtain ⟨delta,C,hd,_,hbound⟩ := dc_slide_consistent_compact_fresh fullMemory (fun _ hj => hj) estimate
      A B (fun _ => g) (fun _ => Q) (k+1) i (k-i) (by omega) (by omega)
      ({0} : Set ℝ) isCompact_singleton
      (fun x hx j _ => by rw [hzero x hx];exact hA j)
      (fun x hx j hj => by rw [hzero x hx];exact hB j hj) (fun _ _ => contDiffAt_const)
      (fun x hx => by rw [hzero x hx];exact hA0) (fun x hx => by rw [hzero x hx];exact hB0)
      (fun _ _ => hQ) (fun _ _ => hpos) (fun _ _ => hpre) (fun _ _ => ha) (fun _ _ => ha0)
      (fun t => canonicalFCPath_symmetric base hb E hE t i)
      (fun j hj => by simp only [fullMemory];omega)
      (fun x hx l hl => by
        rw [hzero x hx,hA0,hB0]
        exact (hcal (i+1+l) (by omega)).trans
          (dc_slide_quadratic_length fullMemory (fun _ hj => hj) estimate Q hQ hpos g (i+1+l)).symm)
    refine IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hd] with t ht
    have ht' : ‖t‖<delta := by simpa only [Metric.mem_ball,dist_zero_right] using ht
    have he := hbound 0 (Set.mem_singleton 0) t (by simpa only [sub_zero] using ht'.le)
    rw [show i+1+(k-i)=k+1 by omega,show i+(k-i)=k by omega] at he
    simpa only [sub_zero,norm_pow,norm_norm] using he
  have hpair (i : ℕ) (hi : i<k) :
      (fun t => dcFreshPairing fullMemory estimate (A t) (B t) g i k-
        inner ℝ (referenceStep Q g i) ((A t k-A t i) (referenceStep Q g k)))
        =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^2) := by
    have hSi : (fun t => S i t-referenceStep Q g i) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖) := by
      simpa only [hS0 i] using differentiable_reference_order (S i) ((hS i (by omega)).differentiableAt (by norm_num))
    have hSk : (fun t => S k t-referenceStep Q g k) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖) := by
      simpa only [hS0 k] using differentiable_reference_order (S k) ((hS k (by omega)).differentiableAt (by norm_num))
    have hT : (fun t => A t k-A t i) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖) := by
      simpa only [hA0,sub_self,sub_zero] using differentiable_reference_order (fun t => A t k-A t i)
        (((hA k).sub (hA i)).differentiableAt (by norm_num))
    exact pairing_reference_order (S i) (S k) (referenceStep Q g i) (referenceStep Q g k)
      (fun t => A t k-A t i) (fun t => ‖t‖) (by simpa using (continuous_norm.tendsto (0 : ℝ))) hSi hSk hT
  have hlead (i : ℕ) (hi : i<k) (t : ℝ) :
      inner ℝ (referenceStep Q g i) ((A t k-A t i) (referenceStep Q g k))=
        t*inner ℝ (canonicalCGStep base g i) L := by
    have ht : A t k-A t i=t • (cumulativeDrift base E k-cumulativeDrift base E i) := by
      change Q+t • cumulativeDrift base E k-(Q+t • cumulativeDrift base E i)=_
      module
    rw [ht,_root_.smul_apply,real_inner_smul_right,
      deferred_response_physical_coordinates base hb g k hN 0 E i hi,zero_mul,zero_add]
  let s := fun i : Fin n => canonicalCGStep base g i.val
  have hLI : LinearIndependent ℝ s := by
    let P := cgOperator (metricRoot base)
    have hP : Function.Injective P := by
      intro v w he
      have hh := congrArg R he
      have hv : R (P v)=v := canonical_primal_dual_cancel base hb v
      have hw : R (P w)=w := canonical_primal_dual_cancel base hb w
      rw [hv,hw] at hh
      exact hh
    have href := reference_window_independent Q hQ hpos g n
      (fun j hj => hpre j (by omega)) (fun i : Fin n => i.val) Fin.val_injective (fun i => i.isLt)
    exact href.map' P.toLinearMap (LinearMap.ker_eq_bot.mpr hP)
  change (fun t : ℝ => R (G t)-t • L) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^2)
  apply fixed_basis_vector_order s hLI _ (fun t : ℝ => ‖t‖^2)
  intro i
  have hmetric (t : ℝ) : inner ℝ (canonicalCGStep base g i.val) (R (G t))=
      inner ℝ (referenceStep Q g i.val) (G t) := (canonical_search_pairing base hb _ _).symm
  by_cases hi : i.val<k
  · have hh := ((hres i.val hi).add (hpair i.val hi)).sub (hfreeze i.val (by omega))
    apply hh.congr_left
    intro t
    change (inner ℝ (S i.val t) (G t)-dcFreshPairing fullMemory estimate (A t) (B t) g i.val k+
      (dcFreshPairing fullMemory estimate (A t) (B t) g i.val k-
        inner ℝ (referenceStep Q g i.val) ((A t k-A t i.val) (referenceStep Q g k))))-
      (inner ℝ (S i.val t) (G t)-inner ℝ (referenceStep Q g i.val) (G t))=_
    rw [hlead i.val hi t]
    change _=inner ℝ (canonicalCGStep base g i.val) (R (G t)-t • L)
    rw [inner_sub_right,real_inner_smul_right,hmetric]
    ring
  · have hik : i.val=k := by have := i.isLt;omega
    have hl : inner ℝ (canonicalCGStep base g i.val) L=0 := by
      rw [hik]
      exact deferred_response_last_coordinate base hb g k hN 0 E
    apply (hfreeze k (by omega)).neg_left.congr_left
    intro t
    have hz : inner ℝ (S k t) (G t)=0 :=
      correctionFree_last_residual m (dc_slide_correction_free fullMemory estimate) (A t) (B t) g k
    rw [hz,zero_sub,neg_neg]
    change _=inner ℝ (canonicalCGStep base g i.val) (R (G t)-t • L)
    rw [inner_sub_right,real_inner_smul_right,hmetric,hl,mul_zero,sub_zero,hik]

end
end krylov.Cancellation
