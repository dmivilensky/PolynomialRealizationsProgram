import krylov.Realization.CompactBudgetConversion
import krylov.Stability.CanonicalContinuity
import krylov.Stability.AnalyticFC
import krylov.Stability.AnalyticRFC
import krylov.Stability.ContDiffXRFC

/-!
Article: Proposition A.7 [prop:conv] of krylov.tex.
Use: discharge the real trajectory smoothness of each implemented method
before applying the common canonical cumulative-injection remainder bound.
Source: genuine executed analytic FC/RFC and primitive C¹ observed-trial XRFC
inductions; actual positive metric-root continuity and exact injection calculus.
-/

namespace krylov.Realization
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- The difference between the true perturbed and actual reference-step cumulative injections in the reference's genuine canonical metric.
Use: XRFC uses its real evaluated reference steps; virtual CG points do not replace the observed trial trajectory.
Article: main_krylov, prop:conv, actual canonical trajectory replacement. -/
def canonicalInjectionReplacement
    (base : X → Matrix (Fin n) (Fin n) ℝ)
    (s : X → ℕ → EuclideanSpace ℝ (Fin n))
    (D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x p : X) (j : ℕ) : EuclideanSpace ℝ (Fin n) :=
  secantInjection (D p) (fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x)) (s p i)) j-
    secantInjection (D p) (fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x)) (s x i)) j

/-- Real finite smooth steps admit the compact-uniform quadratic secant-budget conversion with the genuine positive canonical initial-error factor.
Use: the actual matrix square root, its inverse and the initial-error weight are all discharged from the supplied positive continuous reference family.
Article: main_krylov, prop:conv and lem:U.
Proof: apply the common weighted canonical injection theorem using proved
continuity of the actual positive root and inverse-root error norm, together
with the proved strict positivity of that genuine error norm. -/
theorem compact_metric_secantConversion
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (s : X → ℕ → EuclideanSpace ℝ (Fin n))
    (D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ContinuousOn base K) (hpos : ∀ x∈K, (base x).PosDef)
    (hg : ContinuousOn g K) (hgnz : ∀ x∈K, g x≠0)
    (hs : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => s p i) x)
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => D p i) x)
    (hzero : ∀ x∈K, ∀ i<N, D x i=0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖canonicalInjectionReplacement base s D x (x+h) j‖≤
        C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  exact compact_canonical_secantInjection_weighted s D
    (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))) _ N K hK hs hD hzero
    (canonical_root_continuousOn base K hb hpos)
    (canonical_error_continuousOn base g K hb hg hpos)
    (fun x hx => canonical_error_pos (base x) (hpos x hx) (g x) (hgnz x hx))

/-- The actual full-memory FC cumulative injection has a compact-uniform quadratic reference-step replacement remainder in the genuine canonical metric.
Use: all real finite prefixes share one radius and constant, weighted by the actual initial error; trajectory regularity is proved from real reference domains.
Article: main_krylov, prop:conv, actual compact FC conversion.
Proof: genuine quadratic CG positivity discharges every actual FC solve
and exact-search denominator in the real analytic induction. Apply the
common canonical compact conversion to those actual computed line steps. -/
theorem quadraticFC_compact_secantConversion
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ContinuousOn base K) (hpos : ∀ x∈K, (base x).PosDef)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hg : ∀ x∈K, AnalyticAt ℝ g x) (hgnz : ∀ x∈K, g x≠0)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x))
    (hpre : ∀ x∈K, ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0)
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => D p i) x)
    (hzero : ∀ x∈K, ∀ i<N, D x i=0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖canonicalInjectionReplacement base (fun p => fcStep fullMemory (A p) (g p)) D x (x+h) j‖≤
        C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  apply compact_metric_secantConversion base g _ D N K hK hb hpos
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hgnz _ hD hzero
  intro x hx i hi
  exact (quadraticFC_prefix_analytic A g x (hA x hx) (hg x hx) (cgOperator (base x)) (hAx x hx)
    (cgOperator_positive _ (hpos x hx)).1 (cgOperator_positive _ (hpos x hx)).2 N (hpre x hx)).2 i hi |>.2.contDiffAt

/-- The actual gated repeated RFC cumulative injection has a compact-uniform quadratic reference-step replacement remainder in its genuine canonical metric.
Use: the estimate concerns total real evaluated steps, including every accepted correction query, for each compatible retained-memory regime.
Article: main_krylov, prop:conv, actual compact RFC conversion.
Proof: the real RFC analytic induction derives actual total-step smoothness
from true quadratic models, strict observed gates and nonstagnant reference
searches; the common canonical compact conversion applies to these real steps. -/
theorem quadraticRFC_compact_secantConversion (memory : ℕ → ℕ) (count : ℕ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ContinuousOn base K) (hpos : ∀ x∈K, (base x).PosDef)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hB : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => B p i) x)
    (hg : ∀ x∈K, AnalyticAt ℝ g x) (hgnz : ∀ x∈K, g x≠0)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x))
    (hBx : ∀ x∈K, B x=fun _ => cgOperator (base x))
    (hm : ∀ x∈K, ∀ k, CG.gradient (cgOperator (base x)) (g x) k≠0 → 0<k → 0<memory k)
    (hpre : ∀ x∈K, ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0)
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => D p i) x)
    (hzero : ∀ x∈K, ∀ i<N, D x i=0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖canonicalInjectionReplacement base
        (fun p => probedStep (rfcMethod memory count) (A p) (B p) (g p)) D x (x+h) j‖≤
        C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  apply compact_metric_secantConversion base g _ D N K hK hb hpos
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hgnz _ hD hzero
  intro x hx i hi
  exact (quadraticRFC_prefix_analytic memory count A B g x (hA x hx) (hB x hx) (hg x hx)
    (cgOperator (base x)) (hAx x hx) (hBx x hx) (cgOperator_positive _ (hpos x hx)).1
    (cgOperator_positive _ (hpos x hx)).2 (hm x hx) N (hpre x hx)).2 i hi |>.2.1.contDiffAt

/-- Real full-memory XRFC evaluated steps have a compact-uniform quadratic cumulative-injection replacement remainder under primitive C¹ observed trial coefficients.
Use: the reference term is the actual evaluated XRFC trajectory, which can differ from CG even when virtual outputs coincide.
Article: main_krylov, prop:conv, another actual reference trajectory.
Proof: the actual finite nonzero-trial quadratic basis discharges both
model inverse domains in the genuine C¹ execution induction. Its real queried
steps satisfy the common canonical compact injection theorem. -/
theorem quadraticXRFC_compact_secantConversion (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ContinuousOn base K) (hpos : ∀ x∈K, (base x).PosDef)
    (hA : ∀ x∈K, ∀ i, ContDiffAt ℝ 1 (fun p => A p i) x)
    (hg : ∀ x∈K, ContDiffAt ℝ 1 g x) (hgnz : ∀ x∈K, g x≠0)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x))
    (hpre : ∀ x∈K, ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0)
    (ht : ∀ x∈K, ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _ => cgOperator (base x)) (g x) i)≠0)
    (hT : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k))
    (hD : ∀ x∈K, ∀ i<N, ContDiffAt ℝ 1 (fun p => D p i) x)
    (hzero : ∀ x∈K, ∀ i<N, D x i=0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖canonicalInjectionReplacement base
        (fun p => oneGradientStep (xrfcMethod fullMemory trial) (A p) (g p)) D x (x+h) j‖≤
        C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  apply compact_metric_secantConversion base g _ D N K hK hb hpos
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hgnz _ hD hzero
  intro x hx i hi
  exact (quadraticXRFC_prefix_contDiffAt trial A g x (hA x hx) (hg x hx) (cgOperator (base x)) (hAx x hx)
    (cgOperator_positive _ (hpos x hx)).1 (cgOperator_positive _ (hpos x hx)).2 N
    (hpre x hx) (ht x hx) (hT x hx)).2 i hi
end
end krylov.Realization
