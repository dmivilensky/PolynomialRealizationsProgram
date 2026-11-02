import krylov.Convergence.RestartFrozenOrder
import krylov.Convergence.TableFrozenFC
import krylov.Convergence.OrderCanonicalC3Source

/-!
Article: main_krylov, thm:D, original C3 FC with arbitrary final corrections.
Use: derive the actual degree k+2 from the literal source assumptions,
without supplying a canonical Lipschitz domain or any correction query
bounds. Source: genuine derivative mean value and native frozen execution.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Original continuous D3 yields degree j+2 for the actual j final
full-window model corrections. Article: main_krylov, thm:D. -/
theorem restarted_nativeFC_frozen_C3_degree
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hF : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt G (H z) z)
    (hD : ∀ z,‖metricCoordinates base hb z‖<r → HasFDerivAt H (D z) z)
    (hDc : ContinuousAt D 0)
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧∀ i<k+1,CG.gradient z.1 z.2 i≠0)
    (j : ℕ) : ∃ s : ℝ,0<s ∧s<r ∧∀ x₀ : E,
    let T:=metricCoordinates base hb
    let x:=fcFrozenRestartedPoints T f G s j x₀
    let e:=fun c=>‖T (x c)‖
    (∀ᶠ c in atTop,0<e c →normalizedReference (metricFCOperator T f G H fullMemory s (x c) 0) (G (x c))∈K) →
    Tendsto e atTop (𝓝 0) →
    ∃ C : ℝ,0<C ∧∀ᶠ c in atTop,e (c+1)≤C*(e c)^(j+2) := by
  obtain ⟨s,L,hs,hsr,hLr,hLip⟩:=exists_canonical_hessian_lipschitz_closedBall
    (metricCoordinates base hb) H D hr hD hDc
  refine ⟨s,hs,hsr,?_⟩
  intro x₀
  exact restarted_nativeFC_frozen_normalized_degree base hb (metricCoordinates base hb)
    (metricCoordinates_inverse_symmetric base hb) f G H hs hG₀ hH₀
    (coordinateDerivative_metric_zero base hb H hH₀) hLr hLip
    (fun z hz=>hF z (hz.trans_lt hsr)) (fun z hz=>hG z (hz.trans_lt hsr)) K hK hquad j x₀

end
end krylov.Convergence
