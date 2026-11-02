import krylov.OneGradient.InformedPhysicalRiskLimit
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), original actual informed sharp constant.
Use: identify K_X(c) as the exact least source-wide asymptotic risk
coefficient of the actual informed S implementation on the whole source class.
Source: genuine original all-source upper guarantee and actual original
physical attaining family in its own true metric/reference normalization.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology krylov.Reference krylov.Secant krylov.Information
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The complete original informed constant is exactly the least attainable
source-wide asymptotic risk bound of the real informed S method on every
genuine full reference of dimension at least two. All original physical
sources and all nonnegative individual/zero budget profiles are included;
the metric and penultimate reference-error norm are the source's own.
Use: closes the actual original physical sharp-constant assertion for the
informed native implementation, rather than merely an operator model.
Article: main_krylov, thm:local(b), exact genuine informed S sharp constant.
Proof: the genuine whole-source upper theorem gives K_X(c). The actual
admissible physical attaining family has its true own-normalized risk limit
equal to K_X(c). Any smaller uniform original source bound, evaluated on
that same family at all positive small scales, contradicts its real limit. -/
theorem knownBase_informed_exact_sharp_constant (directions : Bool)
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hcount : referenceAtomCount A hA g=n+2)
    (omega : ℕ → ℝ) (homega : ∀ l<n+1,0≤omega l)
    (w c : ℝ) (hw : 0≤w) (hc : 0≤c) :
    IsLeast {v : ℝ | knownBaseAsymptoticRiskBound directions A g omega w c v}
      (informedConstant (∑ l∈range (n+1),omega l) w c) := by
  let K := informedConstant (∑ l∈range (n+1),omega l) w c
  refine ⟨knownBase_informed_asymptotic_upper_basis directions A hA (by omega) g hcount omega homega w c hw hc,?_⟩
  intro v hv
  obtain ⟨S,hS,hlimit⟩ := knownBase_informed_physical_attainment_basis directions A hA g hcount omega homega w c hw hc
  by_contra hsmall
  have hepsilon : 0<(K-v)/2 := by linarith
  have hbound := hv ((K-v)/2) hepsilon
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0,informedSourceRisk directions A g (S t) t≤v+(K-v)/2 := by
    filter_upwards [hbound,self_mem_nhdsWithin] with t ht htpos
    exact ht (S t) (hS t htpos.le)
  have hle : K≤v+(K-v)/2 := le_of_tendsto hlimit hevent
  linarith

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem knownBase_informed_step_exact_sharp_constant
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hcount : referenceAtomCount A hA g=n+2)
    (omega : ℕ → ℝ) (homega : ∀ l<n+1,0≤omega l)
    (w c : ℝ) (hw : 0≤w) (hc : 0≤c) :
    IsLeast {v : ℝ | knownBaseAsymptoticRiskBound false A g omega w c v}
      (informedConstant (∑ l∈range (n+1),omega l) w c)  := by
  exact knownBase_informed_exact_sharp_constant false A hA g hcount omega homega w c hw hc

end
end krylov.OneGradient
