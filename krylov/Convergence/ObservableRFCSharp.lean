import krylov.Convergence.ObservableRFCMovement
import krylov.Correction.SharpRestart
import krylov.Nonlinear.MetricCoordinates

/-!
Article: main_krylov, apG:Dunif, genuine observable restart geometry.
Use: apply the sharp restart lemma to the actual physical FC direction
inside an RFC cycle. Source: derived stored-window domains and the exact
positive-root primal/dual transport. Canonical FC covariance is not assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
  krylov.Correction krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Both sharp stopping inequalities hold for the genuinely computed
physical direction at every admitted actual RFC history.
Article: main_krylov, apG:Dunif and apG:restart. -/
theorem observable_rfc_sharp_direction
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (B : History (EuclideanSpace ℝ (Fin n)))
    (epsilon bar m ratio : ℝ)
    (I : ObservableRFCInvariant (metricCoordinates base hb) f G x₀ n epsilon bar B)
    (hn : 1≤n) (hsize : B.records.length≤n) (he : 0≤epsilon) (hbar0 : 0≤bar)
    (hsmall : (n:ℝ)*epsilon≤1/128) (hbar : (n:ℝ)*bar≤1/16)
    (hm : 0<m) (hr : 1≤ratio)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hupper : ‖cgOperator base‖≤m^2*ratio^2)
    (hsharp : Real.sqrt n*(4*epsilon)≤Real.sqrt 3/(8*ratio^2)) :
    let T := metricCoordinates base hb
    let g := T.symm B.gradient
    let d := T (rfcFunctionDirection fullMemory B)
    let R := ‖projectedResidual (unitWindow (observablePrimal T B)) g‖
    (0 ≤ inner ℝ B.gradient (rfcFunctionDirection fullMemory B) → ‖g‖≤16*ratio*R) ∧
    (∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (alpha : ℝ),
      ‖A‖≤(9/8:ℝ) → 0<alpha →
      -inner ℝ g d=alpha*inner ℝ d (A d) →
      ‖g‖≤4*ratio^2*(4*R+alpha*‖d‖)) := by
  let T := metricCoordinates base hb
  let s := unitWindow (observablePrimal T B)
  let y := unitWindowImages (observablePrimal T B) (observableDual T B)
  let g := T.symm B.gradient
  let d := T (rfcFunctionDirection fullMemory B)
  let R := ‖projectedResidual s g‖
  have hT := metricCoordinates_inverse_symmetric base hb
  have hdomains := I.domains hT hn hsize he hbar0 hsmall hbar
  have hgram := hdomains.2.2.2
  have hP := observedProjection_residual_bound s (hdomains.2.2.1.trans (by norm_num)) g
  have ho (i : Fin B.pairs.length) : inner ℝ (y i) d=0 := by
    have hh := observable_direction_conjugate T hT B hdomains.1 i
    change inner ℝ (‖observablePrimal T B i‖⁻¹ • observableDual T B i) d=0
    rw [real_inner_smul_left,hh,mul_zero]
  have hy (i : Fin B.pairs.length) : ‖y i-s i‖≤(4*epsilon)/2 := by
    have hh := unitWindow_pair_error (observablePrimal T B) (observableDual T B) I.steps I.pairs i
    exact hh.trans_eq (by ring)
  have hspan : d+cgOperator base g∈Submodule.span ℝ (Set.range s) := by
    have hh := windowDirection_canonical_span base hb B.pairs B.gradient
    change T (windowDirection B.pairs B.gradient)+cgOperator base g∈Submodule.span ℝ (Set.range s) at hh
    dsimp only [d,rfcFunctionDirection]
    rw [selectedWindow_full]
    exact hh
  have hlen : B.pairs.length≤n := by rw [History.pairs_length];exact hsize
  have hlen' : (B.pairs.length:ℝ)≤n := by exact_mod_cast hlen
  have hsharp' : Real.sqrt B.pairs.length*(4*epsilon)≤Real.sqrt 3/(8*ratio^2) :=
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hlen') (by positivity)).trans hsharp
  refine ⟨?_,?_⟩
  · intro hbad
    have hpair : inner ℝ g d=inner ℝ B.gradient (rfcFunctionDirection fullMemory B) := by
      rw [real_inner_comm,metric_primal_dual_pairing T hT,real_inner_comm]
    have hh := sharp_observed_nondescent s y base hb g d m ratio (4*epsilon)
      hm hr hlower hupper hgram (by positivity) hsharp' hy ho hspan (by rw [hpair];exact hbad)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hP (by positivity : 0≤2*(1+ratio)))
    exact hh'.trans (by nlinarith only [mul_le_mul_of_nonneg_right hr (norm_nonneg (projectedResidual s g))])
  · intro A alpha hA halpha hline
    have hh := sharp_observed_short_step s y base hb g d m ratio (4*epsilon) alpha
      hm hr hlower hupper hgram (by positivity) hsharp' hy ho hspan A hA halpha hline
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hP le_rfl) (by positivity : 0≤4*ratio^2))

end
end krylov.Convergence
