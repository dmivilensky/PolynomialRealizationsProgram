import polyak.FareyPlateau.Plateau.LocationTrig

/-! Proposition location with every printed limit, for the actual edge
tunings and arbitrary ways of tending to infinite curvature. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Filter Set Topology

theorem source_location {ι : Type*} {l : Filter ι} {K j k : ℕ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (q : ι→Tuning) (a : ι→ℝ) (D : ℝ)
    (he : ∀i,Chart.coefficients (q i)=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) (a i) D)
    (hdomain : ∀i,aE K j k D<a i) (ha : Tendsto a l atTop) :
    Tendsto (fun i=>(q i).beta) l (𝓝 1) ∧
    Tendsto (fun i=>a i*(1-(q i).beta)^2) l
      (𝓝 (2*Real.tan (Real.pi/(2*k))/Real.sin (Regions.rationalAngle j k))) ∧
    Tendsto (fun i=>(q i).y) l (𝓝 (4*(Real.sin (Real.pi*j/k))^2)) ∧
    Tendsto (fun i=>(q i).kappa) l (𝓝 1) := by
  have hc := rationalCosine_mem hK hf
  have hheight : 0<Chart.rationalHeight j k := by
    linarith [rationalHeight_above hK hf,hc.1]
  have hβ (i) : 0<(q i).beta := by
    apply (Chart.coefficient_quadratic_neg_iff (q i)).mp
    rw [he i]
    change -(a i)<0
    have hp := (aE_pos hK hf D).trans (hdomain i)
    linarith
  let C := fun i=>Chart.coefficientPoint (q i) (hβ i)
  have hC (i) : (C i).val=edgeCoefficients (Chart.rationalCosine j k)
      (Chart.rationalHeight j k) (a i) D := he i
  have ht := location_tuning C a hC hc hheight ha
  have hrecover (i) : Chart.inverseTuning (C i)=q i := Chart.inverseTuning_coefficientPoint _ _
  simp only [hrecover,source_location_constant hK hf] at ht
  have hcos : 2-2*Chart.rationalCosine j k=4*(Real.sin (Real.pi*j/k))^2 := by
    unfold Chart.rationalCosine Regions.rationalAngle
    have hdouble := Real.cos_two_mul (Real.pi*j/k)
    rw [show 2*(Real.pi*j/k)=2*Real.pi*j/k by ring] at hdouble
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*j/k)]
  rw [hcos] at ht
  exact ht

end polyak.FareyPlateau
