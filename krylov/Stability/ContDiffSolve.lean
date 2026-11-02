import krylov.Stability.AnalyticSolve
import Mathlib.Analysis.Matrix.Normed

/-!
Article: main_krylov, lem:U(d), finite C^r observed block solves.
Use: compose the already proved analytic inverse-coefficient functions with
actual C^r observations; arbitrary C² trial rules need not be analytic.
Source: the proved genuine analytic solve calculus and standard C^r composition.
The elementwise matrix norm here is only the finite observed coefficient-space
coordinate norm; no spectral perturbation budget is measured in this norm.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
open scoped Matrix.Norms.Elementwise
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Genuine C^r observed vectors give a genuine C^r computed conjugacy direction on its actual inverse domain.
Use: actual XRFC and smooth coefficient programs can use C² observations rather than analytic trial rules.
Article: main_krylov, lem:U(d).
Proof: the finite conjugacy solve is already proved analytic in its true
observed input coordinates. Compose that actual analytic map with the real
C^r vector observations, at their genuinely nonzero cross-Gram determinant. -/
theorem contDiff_conjugacyDirection {r : WithTop ℕ∞} (s y : X → ι → E) (g : X → E) (x : X)
    (hs : ∀ i, ContDiffAt ℝ r (fun p=>s p i) x)
    (hy : ∀ i, ContDiffAt ℝ r (fun p=>y p i) x) (hg : ContDiffAt ℝ r g x)
    (hu : (crossGram (y x) (s x)).det≠0) :
    ContDiffAt ℝ r (fun p=>conjugacyDirection (s p) (y p) (g p)) x := by
  -- Smoothness is composed from primitive observed data, never assumed for the executed solve.
  let D := (ι → E) × (ι → E) × E
  let z : D := (s x,y x,g x)
  have hs' (i : ι) : AnalyticAt ℝ (fun a : D=>a.1 i) z :=
    ((ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E).analyticAt _).comp analyticAt_fst
  have hy' (i : ι) : AnalyticAt ℝ (fun a : D=>a.2.1 i) z :=
    ((ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E).analyticAt _).comp (analyticAt_fst.comp analyticAt_snd)
  have hg' : AnalyticAt ℝ (fun a : D=>a.2.2) z := analyticAt_snd.comp analyticAt_snd
  have hf := analytic_conjugacyDirection (fun a : D=>a.1) (fun a : D=>a.2.1) (fun a : D=>a.2.2) z hs' hy' hg' hu
  exact hf.contDiffAt.comp x ((contDiffAt_pi.mpr hs).prodMk ((contDiffAt_pi.mpr hy).prodMk hg))
omit [CompleteSpace E] in
/-- Genuine C^r observations and model entries give C^r actual inverse-model coefficients at a true model domain.
Use: virtual XRFC solves inherit exactly the smoothness of actual observations and trial data.
Article: main_krylov, lem:U(d).
Proof: assemble the finite observed vector/matrix/gradient coordinates, use
the already proved actual analytic coefficient function on its true determinant
domain, and apply the standard C^r composition theorem. -/
theorem contDiff_modelCoefficients {r : WithTop ℕ∞} (s : X → ι → E) (H : X → Matrix ι ι ℝ) (g : X → E) (x : X)
    (hs : ∀ i, ContDiffAt ℝ r (fun p=>s p i) x)
    (hH : ∀ i j, ContDiffAt ℝ r (fun p=>H p i j) x) (hg : ContDiffAt ℝ r g x)
    (hu : (H x).det≠0) (i : ι) :
    ContDiffAt ℝ r (fun p=>modelCoefficients (s p) (H p) (g p) i) x := by
  -- Smoothness is composed from primitive observed data, never assumed for the executed solve.
  let D := (ι → E) × Matrix ι ι ℝ × E
  let z : D := (s x,H x,g x)
  have hs' (j : ι) : AnalyticAt ℝ (fun a : D=>a.1 j) z :=
    ((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E).analyticAt _).comp analyticAt_fst
  have hH' (j k : ι) : AnalyticAt ℝ (fun a : D=>a.2.1 j k) z :=
    ((ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ).analyticAt _).comp
      (((ContinuousLinearMap.proj j : Matrix ι ι ℝ →L[ℝ] (ι → ℝ)).analyticAt _).comp
        (analyticAt_fst.comp analyticAt_snd))
  have hg' : AnalyticAt ℝ (fun a : D=>a.2.2) z := analyticAt_snd.comp analyticAt_snd
  have hf := analytic_modelCoefficients (fun a : D=>a.1) (fun a : D=>a.2.1) (fun a : D=>a.2.2) z hs' hH' hg' hu i
  have hd : ContDiffAt ℝ r (fun p : X => ((s p,H p,g p) : D)) x :=
    (contDiffAt_pi.mpr hs).prodMk ((contDiffAt_pi.mpr (fun j=>contDiffAt_pi.mpr (hH j))).prodMk hg)
  exact hf.contDiffAt.comp (g := fun a : D => modelCoefficients a.1 a.2.1 a.2.2 i)
    (f := fun p : X => ((s p,H p,g p) : D)) x hd

omit [CompleteSpace E] in
/-- Genuine C-r observations give C-r actual conjugacy coefficients on the true cross-Gram inverse domain.
Use: Build primitive smooth observed direction rules for the actual named implementations.
Article: main_krylov, def:classes, lem:U(d) and cor:lm.
Proof: The actual conjugacy coefficients are minus the already proved smooth model coefficients with the true image observations as their residual-pairing columns. -/
theorem contDiff_conjugacyCoefficients {r : WithTop ℕ∞} (s y : X → ι → E) (g : X → E) (x : X)
    (hs : ∀ i, ContDiffAt ℝ r (fun p => s p i) x)
    (hy : ∀ i, ContDiffAt ℝ r (fun p => y p i) x) (hg : ContDiffAt ℝ r g x)
    (hu : (crossGram (y x) (s x)).det≠0) (i : ι) :
    ContDiffAt ℝ r (fun p => conjugacyCoefficients (s p) (y p) (g p) i) x := by
  have hm := contDiff_modelCoefficients y (fun p => crossGram (y p) (s p)) g x hy
    (fun i j => (hy i).inner ℝ (hs j)) hg hu i
  convert! hm.neg using 1
  funext p
  simp only [modelCoefficients,conjugacyCoefficients,Pi.neg_apply,neg_neg]

omit [DecidableEq ι] [CompleteSpace E] in
/-- Actual finite physical combinations preserve C^r regularity of their genuine vectors and coefficients.
Use: turn computed model coefficients into true virtual and evaluated displacements.
Article: main_krylov, lem:U(d).
Proof: each actual summand is a C^r scalar-vector product and the physical sum is finite. -/
theorem contDiff_combine {r : WithTop ℕ∞} (s : X → ι → E) (b : X → ι → ℝ) (x : X)
    (hs : ∀ i, ContDiffAt ℝ r (fun p => s p i) x)
    (hb : ∀ i, ContDiffAt ℝ r (fun p => b p i) x) :
    ContDiffAt ℝ r (fun p => combine (s p) (b p)) x := by
  exact ContDiffAt.sum (fun i _ => (hb i).smul (hs i))

omit [CompleteSpace E] in
/-- The true physical finite model correction is C^r in C^r observed vectors, model entries and gradient.
Use: actual virtual corrections need no presumed smooth trajectory or inverse solve.
Article: main_krylov, lem:U(d).
Proof: combine the proved actual C^r inverse coefficients with the genuine C^r stored vectors. -/
theorem contDiff_modelCorrection {r : WithTop ℕ∞} (s : X → ι → E)
    (H : X → Matrix ι ι ℝ) (g : X → E) (x : X)
    (hs : ∀ i, ContDiffAt ℝ r (fun p => s p i) x)
    (hH : ∀ i j, ContDiffAt ℝ r (fun p => H p i j) x) (hg : ContDiffAt ℝ r g x)
    (hu : (H x).det≠0) :
    ContDiffAt ℝ r (fun p => combine (s p) (modelCoefficients (s p) (H p) (g p))) x :=
  contDiff_combine s _ x hs (contDiff_modelCoefficients s H g x hs hH hg hu)

end
end krylov.Stability
