import krylov.Stability.MetricRootRegularity
import krylov.Stability.RFCCompactRemainder
import krylov.Variation.FCResponse

/-!
Article: main_krylov, lem:U(d), genuine joint canonical cycle regularity.
Use: discharge variable-base positive-root dependence in the actual canonical
FC and repeated RFC cycles directly from primitive reference and increment families.
Source: the proved true CFC root/inverse-root C-r calculus, actual physical
matrix/operator identification and genuine quadratic FC/RFC query inductions.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset Filter Topology krylov.Secant krylov.Methods krylov.Reference krylov.Variation
open scoped Matrix.Norms.L2Operator ContDiff
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual canonical FC segment family is jointly C-r in the true varying base and primitive canonical increments.
Use: The actual canonical FC segment family is jointly C-r in the true varying base and primitive canonical increments.
Article: main_krylov, lem:U(d).
Proof: Compose the genuine positive root twice with the actual finite increment sum and the real matrix/operator map. -/
theorem canonicalFCPath_contDiffAt (base : X → Matrix (Fin n) (Fin n) ℝ)
    (E : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (x : X) {r : WithTop ℕ∞}
    (hb : ContDiffAt ℝ r base x) (hpos : ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hE : ∀ l, ContDiffAt ℝ r (fun p => E p l) x) (k : ℕ) :
    ContDiffAt ℝ r (fun p => canonicalFCPath (base p) (E p) 1 k) x := by
  have hR := metricRoot_contDiffAt base x hb hpos
  have hsum := ContDiffAt.sum (s := range k) (fun i _ => hE i)
  have hmatrix := hb.add ((hR.mul hsum).mul hR)
  have hop := matrixOperator_contDiffAt _ x hmatrix
  convert! hop using 1
  funext p
  simp only [canonicalFCPath,cgOperator,cumulativeDrift,one_smul,map_add]

/-- The genuine variable-base canonical segment family is jointly real analytic for analytic primitive data.
Use: The genuine variable-base canonical segment family is jointly real analytic for analytic primitive data.
Article: main_krylov, lem:U(d).
Proof: Apply the proved actual C-r root calculus at real analytic order. -/
theorem canonicalFCPath_analyticAt (base : X → Matrix (Fin n) (Fin n) ℝ)
    (E : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (x : X)
    (hb : AnalyticAt ℝ base x) (hpos : ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hE : ∀ l, AnalyticAt ℝ (fun p => E p l) x) (k : ℕ) :
    AnalyticAt ℝ (fun p => canonicalFCPath (base p) (E p) 1 k) x :=
  (canonicalFCPath_contDiffAt base E x (r := ω) hb.contDiffAt hpos (fun l => (hE l).contDiffAt) k).analyticAt

/-- Zero actual canonical increments give precisely the genuine static base query operator.
Use: Zero actual canonical increments give precisely the genuine static base query operator.
Article: main_krylov, lem:U(d).
Proof: Each true physical increment prefix is zero. -/
theorem canonicalFCPath_at_zero (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, E l=0) :
    canonicalFCPath base E 1=fun _ => cgOperator base := by
  funext k
  simp only [canonicalFCPath,cumulativeDrift,hE,sum_const_zero,Matrix.mul_zero,Matrix.zero_mul,map_zero,one_smul,add_zero]

/-- The genuine canonical output of the actual FC cycle is jointly analytic in its varying quadratic base and actual perturbation variables.
Use: The genuine canonical output of the actual FC cycle is jointly analytic in its varying quadratic base and actual perturbation variables.
Article: main_krylov, lem:U(d).
Proof: Derive real canonical operator analyticity, discharge the true quadratic reference domain, apply actual FC execution induction and compose the genuine varying inverse root. -/
theorem canonicalFC_quadratic_prefix_analytic (base : X → Matrix (Fin n) (Fin n) ℝ)
    (E : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n)) (x : X) (N : ℕ)
    (hb : AnalyticAt ℝ base x) (hpos : ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hE : ∀ l, AnalyticAt ℝ (fun p => E p l) x) (hg : AnalyticAt ℝ g x) (hzero : ∀ l, E x l=0)
    (hpre : ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0) :
    AnalyticAt ℝ (fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
      (fcGradient fullMemory (canonicalFCPath (base p) (E p) 1) (g p) N)) x := by
  -- Primitive base regularity supplies the actual root dependence before the real trajectory induction.
  have hp := hpos.self_of_nhds
  have hG := (quadraticFC_prefix_analytic (fun p => canonicalFCPath (base p) (E p) 1) g x
    (canonicalFCPath_analyticAt base E x hb hpos hE) hg (cgOperator (base x))
    (canonicalFCPath_at_zero _ _ hzero) (cgOperator_positive _ hp).1 (cgOperator_positive _ hp).2 N hpre).1
  have hI : AnalyticAt ℝ (fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹) x :=
    (matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x (r := ω) hb.contDiffAt hpos)).analyticAt
  exact analytic_operator_apply hI hG

/-- The genuine canonical output of actual repeated retained RFC is jointly analytic in the varying base and real search/correction increments.
Use: The genuine canonical output of actual repeated retained RFC is jointly analytic in the varying base and real search/correction increments.
Article: main_krylov, lem:U(d).
Proof: Both actual segment families are analytic by the proved true root calculus. The genuine quadratic RFC induction discharges the real gates, inverses and repeated queries; compose its actual returned gradient with the true varying inverse root. -/
theorem canonicalRFC_quadratic_prefix_analytic (base : X → Matrix (Fin n) (Fin n) ℝ)
    (E F : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n)) (x : X)
    (memory : ℕ → ℕ) (count N : ℕ) (hb : AnalyticAt ℝ base x)
    (hpos : ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hE : ∀ l, AnalyticAt ℝ (fun p => E p l) x) (hF : ∀ l, AnalyticAt ℝ (fun p => F p l) x)
    (hg : AnalyticAt ℝ g x) (hzero : ∀ l, E x l=0 ∧ F x l=0)
    (hm : ∀ k, CG.gradient (cgOperator (base x)) (g x) k≠0 → 0<k → 0<memory k)
    (hpre : ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0) :
    AnalyticAt ℝ (fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
      (probedGradient (rfcMethod memory count) (canonicalFCPath (base p) (E p) 1)
        (canonicalFCPath (base p) (F p) 1) (g p) N)) x := by
  -- Every real correction query is handled by the existing actual RFC induction.
  have hp := hpos.self_of_nhds
  have hG := (quadraticRFC_prefix_analytic memory count
    (fun p => canonicalFCPath (base p) (E p) 1) (fun p => canonicalFCPath (base p) (F p) 1) g x
    (canonicalFCPath_analyticAt base E x hb hpos hE) (canonicalFCPath_analyticAt base F x hb hpos hF) hg
    (cgOperator (base x)) (canonicalFCPath_at_zero _ _ (fun l => (hzero l).1))
    (canonicalFCPath_at_zero _ _ (fun l => (hzero l).2))
    (cgOperator_positive _ hp).1 (cgOperator_positive _ hp).2 hm N hpre).1
  have hI : AnalyticAt ℝ (fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹) x :=
    (matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x (r := ω) hb.contDiffAt hpos)).analyticAt
  exact analytic_operator_apply hI hG
end
end krylov.Stability
