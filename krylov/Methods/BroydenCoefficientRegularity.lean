import krylov.Methods.BroydenCoefficients
import krylov.Methods.BroydenPivots
import krylov.Stability.ContDiffSolve

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, genuine primitive convex Broyden coefficient regularity.
Use: derive actual C-r finite observed-vector coefficients of the real inverse convex Broyden recursion on all true chronological secant and inverse-curvature domains.
Source: genuine coordinate synthesis of the actual endpoint updates, true finite recursive pivot domains and standard real inner-product and reciprocal calculus.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

/-- The genuine finite observed inverse convex Broyden coefficients are C-r at every order on their actual physical recursive pivot domain.
Use: The genuine finite observed inverse convex Broyden coefficients are C-r at every order on their actual physical recursive pivot domain.
Article: main_krylov, def:classes, genuine primitive convex Broyden coefficient regularity.
Proof: Induct through true coefficient pairs; derive both real older model actions, their genuine inverse-curvature pivot and actual endpoint scalar combinations directly in finite observation coordinates. -/
theorem inverseBroydenCoefficients_regular (data : X → Fin m → E) (c : X → ℝ) (θ : ℕ → ℝ)
    (W : List ((Fin m → ℝ) × (Fin m → ℝ))) (v : X → Fin m → ℝ) (x : X) {r : WithTop ℕ∞}
    (hd : ContDiffAt ℝ r data x) (hc : ContDiffAt ℝ r c x) (hv : ContDiffAt ℝ r v x)
    (hpiv : BroydenPivots (c x) θ (W.map (fun p =>
      (observationSynthesis (data x) p.1,observationSynthesis (data x) p.2)))) :
    ContDiffAt ℝ r (fun p => inverseBroydenCoefficients (data p) (c p) θ W (v p)) x := by
  -- Actual finite synthesis evaluates the genuine physical pairings while the real recursion remains in primitive scalar observation coefficients.
  have hsynth (w : X → Fin m → ℝ) (hw : ContDiffAt ℝ r w x) :
      ContDiffAt ℝ r (fun p => observationSynthesis (data p) (w p)) x :=
    contDiff_combine data w x (contDiffAt_pi.mp hd) (contDiffAt_pi.mp hw)
  induction W generalizing v with
  | nil => exact hc.smul hv
  | cons p W ih =>
    have hp : inner ℝ (observationSynthesis (data x) p.1) (observationSynthesis (data x) p.2)≠0 ∧
        inner ℝ (observationSynthesis (data x) p.2)
          (inverseBroydenModel (c x) θ (W.map (fun q =>
            (observationSynthesis (data x) q.1,observationSynthesis (data x) q.2)))
            (observationSynthesis (data x) p.2))≠0 ∧
        BroydenPivots (c x) θ (W.map (fun q =>
            (observationSynthesis (data x) q.1,observationSynthesis (data x) q.2))) := hpiv
    let s := fun z => observationSynthesis (data z) p.1
    let y := fun z => observationSynthesis (data z) p.2
    let Hv := fun z => inverseBroydenCoefficients (data z) (c z) θ W (v z)
    let Hy := fun z => inverseBroydenCoefficients (data z) (c z) θ W p.2
    let ρ := fun z => (inner ℝ (s z) (y z))⁻¹
    let σ := fun z => inner ℝ (y z) (observationSynthesis (data z) (Hy z))
    let a := fun z => inner ℝ (y z) (observationSynthesis (data z) (Hv z))
    let b := fun z => inner ℝ (s z) (observationSynthesis (data z) (v z))
    have hs : ContDiffAt ℝ r s x := hsynth (fun _ => p.1) contDiffAt_const
    have hy : ContDiffAt ℝ r y x := hsynth (fun _ => p.2) contDiffAt_const
    have hHv : ContDiffAt ℝ r Hv x := ih v hv hp.2.2
    have hHy : ContDiffAt ℝ r Hy x := ih (fun _ => p.2) contDiffAt_const hp.2.2
    have hρ : ContDiffAt ℝ r ρ x := (hs.inner ℝ hy).inv hp.1
    have hσ : ContDiffAt ℝ r σ x := hy.inner ℝ (hsynth Hy hHy)
    -- The true inverse-curvature pivot is exactly its genuine physical older-model action, identified by actual coefficient synthesis.
    have hσ0 : σ x≠0 := by
      dsimp only [σ,Hy,y]
      rw [inverseBroydenCoefficients_synthesis]
      exact hp.2.1
    have ha : ContDiffAt ℝ r a x := hy.inner ℝ (hsynth Hv hHv)
    have hb : ContDiffAt ℝ r b x := hs.inner ℝ (hsynth v hv)
    -- Both genuine endpoint coefficient vectors and their actual fixed convex interpolation inherit the real primitive regularity.
    have hdfp : ContDiffAt ℝ r (fun z => Hv z-(a z/σ z) • Hy z+(ρ z*b z) • p.1) x :=
      (hHv.sub ((ha.div hσ hσ0).smul hHy)).add ((hρ.mul hb).smul contDiffAt_const)
    have hbfgs : ContDiffAt ℝ r (fun z => Hv z-(ρ z*b z) • Hy z+
        ((ρ z*b z)-ρ z*(a z-(ρ z*b z)*σ z)) • p.1) x := (hHv.sub ((hρ.mul hb).smul hHy)).add
      (((hρ.mul hb).sub (hρ.mul (ha.sub ((hρ.mul hb).mul hσ)))).smul contDiffAt_const)
    exact ((show ContDiffAt ℝ r (fun _ : X => 1-θ W.length) x from contDiffAt_const).smul hdfp).add
      ((show ContDiffAt ℝ r (fun _ : X => θ W.length) x from contDiffAt_const).smul hbfgs)
end
end krylov.Methods
