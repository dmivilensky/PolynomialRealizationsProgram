import krylov.Methods.ObservationSynthesis
import krylov.Methods.LBFGSRegularity
import krylov.Methods.HistoryWindowCharts
import krylov.Stability.ContDiffSolve

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm and s3:cor:qn, explicit two-loop observed-vector coefficients.
Use: execute actual BFGS/L-BFGS in finite scalar observation coordinates
and prove primitive coefficient regularity on genuine physical curvature pivots.
Source: the standard BFGS two-loop recursion, actual observation synthesis
and real inner-product, reciprocal and finite-coordinate calculus.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

/-- The actual BFGS two-loop recursion in finite scalar observation coordinates with genuine physical inner products.
Use: The actual BFGS two-loop recursion in finite scalar observation coordinates with genuine physical inner products.
Article: main_krylov, cor:lm and s3:cor:qn, explicit two-loop observed-vector coefficients.
Proof: Pull each real inner product through the actual observation synthesis while retaining the true scalar coordinate-vector updates. -/
def inverseBFGSCoefficients (data : Fin m → E) (c : ℝ) :
    List ((Fin m → ℝ) × (Fin m → ℝ)) → (Fin m → ℝ) → (Fin m → ℝ)
  | [],v => c • v
  | (s,y)::W,v =>
      let f := observationSynthesis data
      let ρ := (inner ℝ (f s) (f y))⁻¹
      let a := ρ*inner ℝ (f s) (f v)
      let r := inverseBFGSCoefficients data c W (v-a • y)
      r+(a-ρ*inner ℝ (f y) (f r)) • s

/-- Synthesizing the genuine two-loop coefficient recursion gives exactly the actual physical inverse-BFGS action on the corresponding true observed pairs.
Use: Synthesizing the genuine two-loop coefficient recursion gives exactly the actual physical inverse-BFGS action on the corresponding true observed pairs.
Article: main_krylov, cor:lm and s3:cor:qn, explicit two-loop observed-vector coefficients.
Proof: Induct through the real retained pairs and use actual linear synthesis of each backward and forward update. -/
theorem inverseBFGSCoefficients_synthesis (data : Fin m → E) (c : ℝ)
    (W : List ((Fin m → ℝ) × (Fin m → ℝ))) (v : Fin m → ℝ) :
    observationSynthesis data (inverseBFGSCoefficients data c W v)=
      inverseBFGSApply c (W.map (fun p => (observationSynthesis data p.1,observationSynthesis data p.2)))
        (observationSynthesis data v) := by
  induction W generalizing v with
  | nil => exact map_smul _ _ _
  | cons p W ih =>
    simp only [inverseBFGSCoefficients,List.map_cons,inverseBFGSApply,map_add,map_smul,map_sub,ih]

/-- The true finite two-loop observation coefficients are smooth at every order on their actual nonzero physical curvature domain.
Use: The true finite two-loop observation coefficients are smooth at every order on their actual nonzero physical curvature domain.
Article: main_krylov, cor:lm and s3:cor:qn, explicit two-loop observed-vector coefficients.
Proof: Every genuine variable coefficient vector has a smooth actual finite synthesis. Induct through the true two-loop recursion, deriving each real reciprocal pivot, backward coefficient, recursive vector and forward coefficient. -/
theorem inverseBFGSCoefficients_regular {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (data : X → Fin m → E) (c : X → ℝ) (W : List ((Fin m → ℝ) × (Fin m → ℝ)))
    (v : X → Fin m → ℝ) (x : X) {r : WithTop ℕ∞}
    (hd : ContDiffAt ℝ r data x) (hc : ContDiffAt ℝ r c x) (hv : ContDiffAt ℝ r v x)
    (hpiv : ∀ p∈W, inner ℝ (observationSynthesis (data x) p.1) (observationSynthesis (data x) p.2)≠0) :
    ContDiffAt ℝ r (fun p => inverseBFGSCoefficients (data p) (c p) W (v p)) x := by
  -- Smooth finite synthesis evaluates actual physical inner products while the true recursion remains in explicit scalar observation coordinates.
  have hsynth (w : X → Fin m → ℝ) (hw : ContDiffAt ℝ r w x) :
      ContDiffAt ℝ r (fun p => observationSynthesis (data p) (w p)) x :=
    contDiff_combine data w x (contDiffAt_pi.mp hd) (contDiffAt_pi.mp hw)
  -- Every real backward and forward coefficient uses only genuine nonzero physical curvature pivots.
  induction W generalizing v with
  | nil => exact hc.smul hv
  | cons p W ih =>
    let s := fun z => observationSynthesis (data z) p.1
    let y := fun z => observationSynthesis (data z) p.2
    let ρ := fun z => (inner ℝ (s z) (y z))⁻¹
    let a := fun z => ρ z*inner ℝ (s z) (observationSynthesis (data z) (v z))
    have hs : ContDiffAt ℝ r s x := hsynth (fun _ => p.1) contDiffAt_const
    have hy : ContDiffAt ℝ r y x := hsynth (fun _ => p.2) contDiffAt_const
    have hρ : ContDiffAt ℝ r ρ x := (hs.inner ℝ hy).inv (hpiv p List.mem_cons_self)
    have ha : ContDiffAt ℝ r a x := hρ.mul (hs.inner ℝ (hsynth v hv))
    have hr := ih (fun z => v z-a z • p.2) (hv.sub (ha.smul contDiffAt_const))
      (fun q hq => hpiv q (List.mem_cons_of_mem p hq))
    have hβ := ha.sub (hρ.mul (hy.inner ℝ (hsynth _ hr)))
    exact hr.add (hβ.smul contDiffAt_const)
end
end krylov.Methods
