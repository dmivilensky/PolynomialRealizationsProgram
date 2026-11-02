import jacobi.Jacobi.ScaledState
import jacobi.Jacobi.HalfSpectrumComparison
import jacobi.Bessel.OrdinaryPhase

/-!
Article: jacobi, Proposition B.1.
The original finite Jacobi wave is rescaled at its actual frequency.
Its true phase integral has its literal perturbed Bessel derivative.
Original finite zeros and zero-free nodal intervals are preserved under
this positive scaling; they fix the exact phase numbering.
Use: all open-set and convexity hypotheses of the original finite phase construction are discharged explicitly.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The positive rescaling has precisely the physical open comparison interval.
Use: all open-set and convexity hypotheses of the original finite phase construction are discharged explicitly.
Article: jacobi, Proposition B.1.
Proof: multiply the two interval inequalities by the actual positive frequency. -/
theorem scaled_domain {N : ℝ} (hN : 0<N) :
    ((fun x : ℝ => x/N) ⁻¹' Ioo 0 Real.pi)=Ioo 0 (N*Real.pi) := by
  ext x
  change (0<x/N ∧ x/N<Real.pi) ↔ (0<x ∧ x<N*Real.pi)
  rw [div_pos_iff_of_pos_right hN,div_lt_iff₀ hN,mul_comm Real.pi N]

/-- The original true finite Jacobi phase at Bessel-scaled arguments.
Use: its genuine numbered zero values and actual differential equation produce the sharp uniform angular expansion.
Article: jacobi, Proposition B.1.
-/
def scaledPhase (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ)
    (hN : 0<frequency a b n) (base x : ℝ) : ℝ :=
  (scaledState a b ha hb n hN).phase base x

/-- The actual scaled finite phase has exactly the inverse-square Bessel phase derivative with the original smooth finite perturbation.
Use: discharges the phase-equation input of the proved uniform averaging theorem for the original Jacobi polynomial.
Article: jacobi, Proposition B.1.
Proof: the actual physical domain is open and convex. The base is a true
original wave zero. Apply the true phase-integral derivative and exact
rotating-state identity, then substitute the actual rescaled coefficient. -/
theorem scaledPhase_hasDerivAt {a b base x : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ)
    (hN : 0<frequency a b n) (hbase : base∈Ioo 0 (frequency a b n*Real.pi))
    (hx : x∈Ioo 0 (frequency a b n*Real.pi))
    (hz : liouville a b n (base/frequency a b n)=0) :
    HasDerivAt (scaledPhase a b ha hb n hN base)
      (1+(endpointCorrection a/x^2+regularPotential a b (x/frequency a b n)/(frequency a b n)^2)*
        sin (scaledPhase a b ha hb n hN base x)^2) x := by
  -- The genuine original zero fixes the actual sine phase; no independent phase function or zero correspondence is assumed.
  let S := scaledState a b ha hb n hN
  have hdomain := scaled_domain hN
  have hconv : Convex ℝ ((fun x : ℝ => x/frequency a b n) ⁻¹' Ioo 0 Real.pi) := by rw [hdomain]; exact convex_Ioo _ _
  have hopen : IsOpen ((fun x : ℝ => x/frequency a b n) ⁻¹' Ioo 0 Real.pi) := by rw [hdomain]; exact isOpen_Ioo
  have hb' : base/frequency a b n∈Ioo 0 Real.pi := by change base∈((fun x : ℝ => x/frequency a b n) ⁻¹' Ioo 0 Real.pi); rwa [hdomain]
  have hx' : x/frequency a b n∈Ioo 0 Real.pi := by change x∈((fun x : ℝ => x/frequency a b n) ⁻¹' Ioo 0 Real.pi); rwa [hdomain]
  have h := S.phase_hasDerivAt hconv hb' hx'
  have he := S.phaseDensity_at_zero hopen hconv hb' hx' hz
  rw [scaledState_potential ha hb n hN hx.1] at he
  rw [he] at h
  change HasDerivAt (S.phase base) (1+(endpointCorrection a/x^2+
    regularPotential a b (x/frequency a b n)/(frequency a b n)^2)*sin (S.phase base x)^2) x
  convert h using 1
  ring

/-- The actual finite angle times its original positive frequency is a true scaled solution zero in the physical domain.
Use: all finite phase bases and numbered levels refer to the actual sorted original Jacobi zeros.
Article: jacobi, Proposition B.1.
Proof: cancel the actual nonzero frequency and use the genuine finite angle zero and interval theorems. -/
theorem scaledAngle_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ}
    (hN : 0<frequency a b n) (hk : k<n) :
    frequency a b n*finiteAngleAt a b ha hb n k∈Ioo 0 (frequency a b n*Real.pi) ∧
      liouville a b n ((frequency a b n*finiteAngleAt a b ha hb n k)/frequency a b n)=0 := by
  have htheta := finiteAngleAt_interval ha hb hk
  refine ⟨⟨mul_pos hN htheta.1,mul_lt_mul_of_pos_left htheta.2 hN⟩,?_⟩
  rw [mul_div_cancel_left₀ _ hN.ne']
  exact finiteAngleAt_is_zero ha hb hk

end
end jacobi.Jacobi
