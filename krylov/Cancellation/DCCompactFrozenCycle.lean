import krylov.Cancellation.DCConsistentResidual
import krylov.Cancellation.DeferredRadauComparison
import krylov.Cancellation.DCFrozenReconstruction
import krylov.Stability.CompactPairingFreeze
import krylov.Stability.CompactBasisInverse
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), full native compact C-one cycle reconstruction.
Use: prove one actual full-vector quadratic remainder on compact reference
families and every simultaneous true source perturbation under C-one data.
Source: genuine native compact fresh residuals, proved compact outer-step
freezing and true uniform inverse-reference-basis reconstruction.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Consistent full-memory native exact-search DC-slide has one genuine
compact-uniform full physical vector expansion in its true frozen fresh
coordinates, under C-one original observed estimates alone.
Use: all source perturbations in the genuine parameter tube share the same
radius and constant; axiswise remainders are not assumed to be uniform.
Article: main_krylov, apH:dcs2(b), compact full native cycle reconstruction.
Proof: derive actual C-one steps and terminal gradients from original
primitive observed coefficients. Native compact residual cancellation leaves
the true newest defect; compact bilinear estimates freeze both actual outer
steps and the moving paired step with quadratic cost. Assemble the genuine
scalar bounds with a common finite radius. The full true CG reference basis
is independent and its actual inverse transpose is uniformly bounded on the
compact family, so it reconstructs the full vector with the same quadratic order. -/
theorem dc_slide_consistent_compact_frozen_cycle
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hfull : k+1=n) (K : Set X) (hK : IsCompact K)
    (hp : ∀ x∈K,(base x).PosDef)
    (hcount : ∀ x (hx : x∈K),referenceAtomCount (base x) (hp x hx) (g x)=n)
    (hA : ∀ x∈K,∀ j<n,ContDiffAt ℝ 1 (fun p => A p j) x)
    (hB : ∀ x∈K,∀ j<n,ContDiffAt ℝ 1 (fun p => B p j) x)
    (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hAx : ∀ x∈K,A x=fun _ => cgOperator (base x))
    (hBx : ∀ x∈K,B x=fun _ => cgOperator (base x))
    (hAsym : ∀ p j,(A p j).toLinearMap.IsSymmetric)
    (ha : ∀ x∈K,∀ j<n,
      let Q := cgOperator (base x)
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => Q) (fun _ => Q) (g x) j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,∀ j<n,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j))
    (hcal : ∀ x∈K,∀ j<n,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j)=CG.length (cgOperator (base x)) (g x) j) :
    let m := dcSlideMethod fullMemory estimate
    let S := fun p j => probedStep m (A p) (B p) (g p) j
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤delta →
      ‖probedGradient m (A y) (B y) (g y) n-
        frozenFreshGradient (fun i : Fin n => S x i.val) (S x k) (A y) k‖≤C*‖y-x‖^2 := by
  let m := dcSlideMethod fullMemory estimate
  let Q := fun x => cgOperator (base x)
  let S := fun p j => probedStep m (A p) (B p) (g p) j
  let G := fun p => probedGradient m (A p) (B p) (g p) n
  let s := fun x (i : Fin n) => S x i.val
  have hm : CGConsistent m := dc_slide_consistent fullMemory (fun _ hj => hj) estimate
  have hQ (x : X) (hx : x∈K) := cgOperator_positive (base x) (hp x hx)
  have hpre (x : X) (hx : x∈K) (j : ℕ) (hj : j<n) : CG.gradient (Q x) (g x) j≠0 :=
    cg_nonstagnation _ (hp x hx) _ j (by rw [hcount x hx];exact hj)
  have hsmooth (x : X) (hx : x∈K) := dc_slide_smoothCycleAt fullMemory (fun _ hj => hj) estimate
    (Q x) (hQ x hx).1 (hQ x hx).2 (g x) n (hpre x hx) 1 (ha x hx) (ha0 x hx)
  have hS (x : X) (hx : x∈K) (j : ℕ) (hj : j<n) : ContDiffAt ℝ 1 (fun p => S p j) x :=
    (smoothProbed_fields_regular m hm A B g x n (hA x hx) (hB x hx) (hg x hx) (Q x)
      (hAx x hx) (hBx x hx) (hQ x hx).1 (hQ x hx).2 (hpre x hx) (hsmooth x hx) j hj).2.2.1
  have hG (x : X) (hx : x∈K) : ContDiffAt ℝ 1 G x := smoothProbed_gradient_regular m hm A B g x n
    (hA x hx) (hB x hx) (hg x hx) (Q x) (hAx x hx) (hBx x hx) (hQ x hx).1 (hQ x hx).2 (hpre x hx) (hsmooth x hx)
  have hSref (x : X) (hx : x∈K) (j : ℕ) : S x j=referenceStep (Q x) (g x) j := by
    dsimp only [S]
    rw [hAx x hx,hBx x hx]
    exact quadratic_probedStep_eq_cg m hm (Q x) (hQ x hx).1 (hQ x hx).2 (g x) j
  have hG0 (x : X) (hx : x∈K) : G x=0 := by
    dsimp only [G]
    rw [hAx x hx,hBx x hx]
    exact (quadratic_gradient_eq_cg m hm (Q x) (hQ x hx).1 (hQ x hx).2 (g x) n).trans
      ((cg_stopping_iff _ (hp x hx) _ n).mpr (by rw [hcount x hx]))
  have hLI (x : X) (hx : x∈K) : LinearIndependent ℝ (s x) := by
    have he : s x=fun i : Fin n => referenceStep (Q x) (g x) i.val := funext fun i => hSref x hx i.val
    rw [he]
    exact reference_window_independent (Q x) (hQ x hx).1 (hQ x hx).2 (g x) n (hpre x hx)
      (fun i : Fin n => i.val) Fin.val_injective (fun i => i.isLt)
  let r := fun (i : Fin n) (p : X × X) =>
    inner ℝ (S p.1 i.val) (G p.2)-inner ℝ (S p.1 i.val) ((A p.2 k-A p.2 i.val) (S p.1 k))
  have hr (i : Fin n) : ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤delta →
      ‖r i (x,y)‖≤C*‖y-x‖^2 := by
    obtain ⟨dt,Ct,hdt,hCt,hterminal⟩ := compact_terminal_pairing_freeze (fun p => S p i.val) G K hK
      (fun x hx => hS x hx i.val i.isLt) hG hG0
    by_cases hi : i.val<k
    · obtain ⟨df,Cf,hdf,hCf,hfresh⟩ := compact_fresh_pairing_freeze (fun p => S p i.val) (fun p => S p k)
        (fun p => A p k-A p i.val) K hK (fun x hx => hS x hx i.val i.isLt)
        (fun x hx => hS x hx k (by omega))
        (fun x hx => (hA x hx k (by omega)).sub (hA x hx i.val i.isLt))
        (fun x hx => by rw [hAx x hx,sub_self])
      obtain ⟨dr,Cr,hdr,hCr,hres⟩ := dc_slide_consistent_compact_fresh fullMemory (fun _ hj => hj) estimate A B g Q
        n i.val (k-i.val) (by omega) (by omega) K hK hA hB hg hAx hBx
        (fun x hx => (hQ x hx).1) (fun x hx => (hQ x hx).2) hpre ha ha0
        (fun p => hAsym p i.val) (fun j hj => by simp only [fullMemory];omega)
        (fun x hx l hl => by
          rw [hAx x hx,hBx x hx]
          exact (hcal x hx (i.val+1+l) (by omega)).trans
            (dc_slide_quadratic_length fullMemory (fun _ hj => hj) estimate (Q x)
              (hQ x hx).1 (hQ x hx).2 (g x) (i.val+1+l)).symm)
      refine ⟨min dr (min df dt),Cr+Cf+Ct,lt_min hdr (lt_min hdf hdt),by positivity,?_⟩
      intro x hx y hy
      have hrb := hres x hx y (hy.trans (min_le_left _ _))
      rw [show i.val+1+(k-i.val)=n by omega,show i.val+(k-i.val)=k by omega] at hrb
      have hfb := hfresh x hx y (hy.trans ((min_le_right _ _).trans (min_le_left _ _)))
      have htb := hterminal x hx y (hy.trans ((min_le_right _ _).trans (min_le_right _ _)))
      have heq : r i (x,y)=
          (inner ℝ (S y i.val) (G y)-dcFreshPairing fullMemory estimate (A y) (B y) (g y) i.val k)+
          (dcFreshPairing fullMemory estimate (A y) (B y) (g y) i.val k-
            inner ℝ (S x i.val) ((A y k-A y i.val) (S x k)))-
          (inner ℝ (S y i.val) (G y)-inner ℝ (S x i.val) (G y)) := by dsimp only [r];ring
      rw [heq]
      calc
        _≤(‖inner ℝ (S y i.val) (G y)-dcFreshPairing fullMemory estimate (A y) (B y) (g y) i.val k‖+
            ‖dcFreshPairing fullMemory estimate (A y) (B y) (g y) i.val k-
              inner ℝ (S x i.val) ((A y k-A y i.val) (S x k))‖)+
            ‖inner ℝ (S y i.val) (G y)-inner ℝ (S x i.val) (G y)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _≤(Cr*‖y-x‖^2+Cf*‖y-x‖^2)+Ct*‖y-x‖^2 := add_le_add (add_le_add hrb hfb) htb
        _=(Cr+Cf+Ct)*‖y-x‖^2 := by ring
    · have hik : i.val=k := by have := i.isLt;omega
      refine ⟨dt,Ct,hdt,hCt,?_⟩
      intro x hx y hy
      have ht := hterminal x hx y hy
      have hz : inner ℝ (S y k) (G y)=0 := by
        change inner ℝ (probedStep m (A y) (B y) (g y) k) (probedGradient m (A y) (B y) (g y) n)=0
        simpa only [hfull] using
          correctionFree_last_residual m (dc_slide_correction_free fullMemory estimate) (A y) (B y) (g y) k
      change ‖inner ℝ (S x i.val) (G y)-inner ℝ (S x i.val) ((A y k-A y i.val) (S x k))‖≤_
      rw [hik,sub_self,_root_.zero_apply,inner_zero_right,sub_zero]
      rw [hik,hz,zero_sub,norm_neg] at ht
      exact ht
  obtain ⟨delta,C,hd,hC,hcoord⟩ := finite_compact_quadratic_bounds r K hr
  obtain ⟨M,hM,hreconstruct⟩ := compact_basis_inverse_bound s K hK
    (fun x hx i => hS x hx i.val i.isLt) hLI
  refine ⟨delta,M*Real.sqrt n*C,hd,by positivity,?_⟩
  intro x hx y hy
  let v := G y-frozenFreshGradient (s x) (S x k) (A y) k
  have hv : ‖projectedResidual (s x) v‖≤Real.sqrt n*(C*‖y-x‖^2) := by
    apply coordinate_norm_le_sqrt_card _ (mul_nonneg hC (sq_nonneg _))
    intro i
    change |inner ℝ (s x i) (G y-frozenFreshGradient (s x) (S x k) (A y) k)|≤_
    rw [inner_sub_right,frozen_fresh_gradient_coordinates (s x) (hLI x hx)]
    simpa only [Real.norm_eq_abs] using hcoord x hx y hy i
  exact (hreconstruct x hx v).trans ((mul_le_mul_of_nonneg_left hv hM).trans_eq (by ring))

end
end krylov.Cancellation
