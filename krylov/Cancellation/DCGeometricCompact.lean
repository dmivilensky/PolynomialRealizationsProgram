import krylov.Cancellation.DCReferenceDamping
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), actual compact arithmetic geometric forgetting.
Use: control every actual old residual by genuine chronological geometric
weights and one common quadratic remainder on the real native arithmetic DC run.
Source: actual C-one compact reference-weight residual expansion and proved
native arithmetic reference multipliers, with all physical domains derived.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The original observed arithmetic DC implementation damps every stale
physical defect geometrically, with one true compact-uniform quadratic
remainder under the source primitive C-one estimate hypothesis.
Use: the contraction factor is derived from the native observed policy and
original physical spectral class, rather than assumed for scalar multipliers.
Article: main_krylov, thm:dcs(c), full compact arithmetic geometric forgetting.
Proof: actual quadratic histories derive positive chosen estimates and their
true class spectral multiplier bound. Primitive observed C-one coefficients
give the genuine compact reference-weight residual expansion. The real
chronological finite product estimate yields exactly the geometric age weights;
the native residual differs by at most the same common quadratic remainder. -/
theorem dc_gauss_radau_compact_geometric
    (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (base : X → Matrix (Fin n) (Fin n) ℝ)
    (T i N : ℕ) (hT : i+N<T) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K,∀ k<T,ContDiffAt ℝ 1 (fun p => A p k) x)
    (hB : ∀ x∈K,∀ k<T,ContDiffAt ℝ 1 (fun p => B p k) x)
    (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hAx : ∀ x∈K,A x=fun _ => cgOperator (base x)) (hBx : ∀ x∈K,B x=fun _ => cgOperator (base x))
    (hb : ∀ x∈K,(base x).PosDef)
    (hlo : ∀ x∈K,(base x-mu • 1).PosSemidef)
    (hhi : ∀ x∈K,(L • 1-base x).PosSemidef)
    (hpre : ∀ x∈K,∀ k<T,CG.gradient (cgOperator (base x)) (g x) k≠0)
    (ha : ∀ x∈K,∀ k<T,
      let H := methodRun (dcSlideMethod memory (dcGaussRadauEstimate memory mu L)) (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) k
      ContDiffAt ℝ 1 (historyEstimateChart (dcGaussRadauEstimate memory mu L) H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (hAi : ∀ p : X,(A p i).toLinearMap.IsSymmetric)
    (hkeep : ∀ j<N,(i+1+j)-1-i<memory (i+1+j)) :
    let estimate := dcGaussRadauEstimate memory mu L (n := n)
    let m := dcSlideMethod memory estimate
    let rho := (L-mu)/(L+mu)
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤δ →
      |inner ℝ (probedStep m (A y) (B y) (g y) i) (probedGradient m (A y) (B y) (g y) (i+1+N))|≤
        (∑ j∈Finset.range N,rho^(N-1-j)*|dcFreshPairing memory estimate (A y) (B y) (g y) i (i+1+j)|)+
          C*‖y-x‖^2 := by
  let estimate := dcGaussRadauEstimate memory mu L (n := n)
  let m := dcSlideMethod memory estimate
  let rho := (L-mu)/(L+mu)
  have href (x : X) (hx : x∈K) (k : ℕ) (hk : k<T) :=
    dc_gauss_radau_reference_damping memory hm (base x) (hb x hx) mu L hmu hmuL
      (hlo x hx) (hhi x hx) (g x) k (hpre x hx k hk)
  obtain ⟨δ,C,hδ,hC,hbound⟩ := dc_slide_compact_residual_expansion memory hm estimate A B g
    (fun x => cgOperator (base x)) T i N hT K hK hA hB hg hAx hBx
    (fun x hx => (cgOperator_positive (base x) (hb x hx)).1)
    (fun x hx => (cgOperator_positive (base x) (hb x hx)).2)
    hpre ha (fun x hx k hk => (href x hx k hk).1) hAi hkeep (freezeSearch := true)
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx y hy
  let e := fun l => 1-dcSearchedLength memory estimate (A x) (B x) (g x) (i+1+l)/
    estimate (methodRun m (A x) (B x) (g x) (i+1+l))
  let d := fun j => dcFreshPairing memory estimate (A y) (B y) (g y) i (i+1+j)
  let r := inner ℝ (probedStep m (A y) (B y) (g y) i) (probedGradient m (A y) (B y) (g y) (i+1+N))
  let S := ∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,e l)*d j
  have he : ∀ l<N,|e l|≤rho := by
    intro l hl
    dsimp only [e]
    rw [hAx x hx,hBx x hx]
    exact (href x hx (i+1+l) (by omega)).2
  have hp : |S|≤∑ j∈Finset.range N,rho^(N-1-j)*|d j| := residual_product_geometric e d N rho he
  have hr : |r-S|≤C*‖y-x‖^2 := hbound x hx y hy
  calc
    |r|=|S+(r-S)| := by congr 1;ring
    _≤|S|+|r-S| := by simpa only [Real.norm_eq_abs] using norm_add_le S (r-S)
    _≤(∑ j∈Finset.range N,rho^(N-1-j)*|d j|)+C*‖y-x‖^2 := add_le_add hp hr

end
end krylov.Cancellation
