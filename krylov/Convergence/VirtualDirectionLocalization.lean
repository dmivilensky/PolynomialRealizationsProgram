import krylov.Convergence.VirtualDirectionFields
import krylov.Convergence.OneGradientC1Localization

/-!
Article: main_krylov, thm:V, literal V1--V3 native localization.
Use: derive every real scalar XRFC query bound uniformly over the original
compact unit-reference direction family. Only genuine local gradient/Hessian
data and the primitive observed C-two positive homogeneous trial rule are
assumed. The physical compact set, all auxiliary oracle extensions, source
domains, and actual intermediate and unevaluated output bounds are derived.
Source: genuine one-gradient C-one localization and actual XRFC trial calculus.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
  krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual scalar-function XRFC evaluated point. Article: thm:V. -/
def xrfcDFunctionPoint (trial : History E → ℝ) (G : E → E) (x₀ : E) (i : ℕ) : E :=
  oneGradientFunctionPoint (xrfcDMethod fullMemory trial) G x₀ i

/-- The actual scalar-function XRFC virtual output, genuinely absent
from its query transcript. Article: main_krylov, thm:V. -/
def xrfcDFunctionOutput (trial : History E → ℝ) (G : E → E) (x₀ : E) : E :=
  oneGradientFunctionOutput (xrfcDMethod fullMemory trial) G x₀ n

/-- Literal V1--V3 imply compact-uniform localization of the entire true
scalar XRFC cycle and its virtual output. This uses only a continuous true
Hessian, weaker than the C-three transfer hypotheses of thm:V. -/
theorem xrfcDFunction_compact_localization
    (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcDMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (G : E → E) (H : E → E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) (hH : ContinuousAt H 0)
    (hG : ∀ x∈ball 0 r,HasFDerivAt G (H x) x) :
    ∃ ep D : ℝ,0<ep ∧0<D ∧∀ ε : ℝ,0<ε → ε<ep →∀ u∈U,
      (∀ i≤n,xrfcDFunctionPoint trial G (ε • u) i∈ball 0 r ∧
        ‖xrfcDFunctionPoint trial G (ε • u) i‖≤ε*D) ∧
      (xrfcDFunctionOutput trial G (ε • u)∈ball 0 r ∧‖xrfcDFunctionOutput trial G (ε • u)‖≤ε*D) ∧
      (∀ i<n,‖(xrfcDMethod fullMemory trial).step
        (oneGradientFunctionRun (xrfcDMethod fullMemory trial) G (ε • u) i)‖≤ε*D) ∧
      ‖(xrfcDMethod fullMemory trial).output
        (oneGradientFunctionRun (xrfcDMethod fullMemory trial) G (ε • u) n)‖≤ε*D := by
  let Q := cgOperator base
  let K := Q '' U
  have hK : IsCompact K := hU.image Q.continuous
  have hQ : IsSelfAdjoint Q := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (cgOperator_positive base hb).1
  have hfield g (hg : g∈K) :
      ContDiffAt ℝ 1 (oneGradientFiniteField (xrfcDMethod fullMemory trial) Q n) (g,0) := by
    obtain ⟨u,hu,rfl⟩ := hg
    exact xrfcDFiniteField_contDiffAt trial Q (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 n (Q u)
      (fun i hi=>cg_nonstagnation base hb (Q u) i (by rw [hcount u hu]; exact hi))
      (fun i hi=>(ht u hu i hi).ne') (hT u hu)
  have hstep g (hg : g∈K) i (hi : i<n) : ContDiffAt ℝ 1
      (fun z : E × (Fin n → E →L[ℝ] E)=>oneGradientStep (xrfcDMethod fullMemory trial)
        (fcFiniteOperatorPath Q n z.2) z.1 i) (g,0) :=
    contDiffAt_pi.mp (hfield g hg).fst ⟨i,hi⟩
  have hout g (hg : g∈K) : ContDiffAt ℝ 1
      (fun z : E × (Fin n → E →L[ℝ] E)=>(xrfcDMethod fullMemory trial).output
        (oneGradientRun (xrfcDMethod fullMemory trial) (fcFiniteOperatorPath Q n z.2) z.1 n)) (g,0) :=
    (hfield g hg).snd
  obtain ⟨R,hR⟩ := hU.exists_bound_of_continuousOn (continuous_id.continuousOn)
  obtain ⟨ep,D,hep,hD,hbounds⟩ := compact_oneGradient_C1_localization (xrfcDMethod fullMemory trial) Q hQ K hK
    hstep hout (fun A g c hc=>xrfcD_policy_homogeneous trial hhom A g c hc n)
    G H r (max R 1) hr (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hG₀ hH₀ hH hG
  exact ⟨ep,D,hep,hD,fun ε hε he u hu=>
    hbounds ε hε he u ((hR u hu).trans (le_max_left _ _)) ⟨u,hu,rfl⟩⟩

end
end krylov.Convergence
