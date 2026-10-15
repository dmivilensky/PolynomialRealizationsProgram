import «2610.05164v2».LocalObstruction.SingleFamilies
import «2610.05164v2».LocalObstruction.GroundSymmetry

/-!
Article: 2610.05164v2, Theorem 6.1.
Lemma 26(ii): the printed variation formula for the actual ground coupling, with the actual positive
ground state and no eigenvalue derivative assumption.
Use: `«2610.05164v2».LocalObstruction.groundCoupling_density_derivative` feeds
`«2610.05164v2».LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Filters «2610.05164v2».GroundState «2610.05164v2».Sobolev
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
The precise assertion is `signedJost hm (-groundParameter hm hn) x*signedJost hm
(-groundParameter hm hn) (-x)= (H1.rep G.u x)^2/(groundLeftAmplitude G)^2`.

Use: `«2610.05164v2».LocalObstruction.groundJost_weighted_product` rewrites with this identity
to establish `(∫ x,v x*signedJost hm (-groundParameter hm hn)
x*signedJost hm (-groundParameter hm hn) (-x))= (∫ x,v x*(H1.rep G.u x)^2)/(groundLeftAmplitude
G)^2`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem groundJost_product {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun x => exp (-x)*m x))
    (he : ∀ x,m (-x)=m x) (x : ℝ) :
    signedJost hm (-groundParameter hm hn) x*signedJost hm (-groundParameter hm hn) (-x)=
      (H1.rep G.u x)^2/(groundLeftAmplitude G)^2 := by
  rw [signedJost_at_ground G hM,signedJost_at_ground G hM,neg_neg,ground_even G he,exp_neg]
  field_simp [(exp_pos x).ne',(groundLeftAmplitude_positive G hM).ne']


 /--
The precise assertion is `(∫ x,v x*signedJost hm (-groundParameter hm hn) x*signedJost hm
(-groundParameter hm hn) (-x))= (∫ x,v x*(H1.rep G.u x)^2)/(groundLeftAmplitude G)^2`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_density_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
groundCoupling (m+ε • v)) (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/
(∫ x,m x*(H1.rep G.u x)^2)) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem groundJost_weighted_product {m v : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun x => exp (-x)*m x))
    (he : ∀ x,m (-x)=m x) :
    (∫ x,v x*signedJost hm (-groundParameter hm hn) x*signedJost hm (-groundParameter hm hn) (-x))=
      (∫ x,v x*(H1.rep G.u x)^2)/(groundLeftAmplitude G)^2 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [mul_assoc,groundJost_product G hM he]
    ring)

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => groundCoupling (m+ε • v))
(-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/ (∫ x,m x*(H1.rep G.u
x)^2)) 0`.

Use: `«2610.05164v2».LocalObstruction.groundObservationWitness` uses this derivative formula in
the displayed construction of `groundObservationWitness`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem groundCoupling_density_derivative {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hM : Integrable (fun x => exp (-x)*m x)) (he : ∀ x,m (-x)=m x)
    (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v)
    (G : GroundWitness hm (fun x => (hn x).le)) :
    HasDerivAt (fun ε : ℝ => groundCoupling (m+ε • v))
      (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/
        (∫ x,m x*(H1.rep G.u x)^2)) 0 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let K := fun ε : ℝ => groundCoupling (m+ε • v)
  let b := deriv K 0
  have hK : HasDerivAt K b 0 :=
    (groundCoupling_single_c1 hm hc hn hM he hv hvc hvcomp).differentiableAt
      (by norm_num : (1:ℕ∞ω)≠0) |>.hasDerivAt
  have hk : K 0=groundParameter hm (fun x => (hn x).le) := by
    dsimp only [K]
    simp only [zero_smul,add_zero]
    exact groundCoupling_actual hm _ G.mass_positive
  let q := (-K 0)/2*(∫ x,v x*signedJost hm (-K 0) x*signedJost hm (-K 0) (-x))
  let c := (1/2:ℝ)*(∫ x,m x*signedJost hm (-K 0) x*signedJost hm (-K 0) (-x))
  have hq : HasDerivAt (fun ε : ℝ => singleTransmission hm hv (ε,-K 0)) q 0 :=
    signedTransmission_density_derivative hm hv _ he
  have hs0 : (fun s : ℝ => singleTransmission hm hv (0,s))=signedTransmission hm := by
    funext s
    unfold singleTransmission
    congr 1
    simp
  have hcp : HasDerivAt (fun s : ℝ => singleTransmission hm hv (0,s)) c (-K 0) := by
    rw [hs0]
    exact signedTransmission_scale_derivative hm _ he
  have hbase : singleTransmission hm hv (0,-K 0)=0 := by
    change (fun s : ℝ => singleTransmission hm hv (0,s)) (-K 0)=0
    rw [hs0,hk]
    exact signedTransmission_at_ground G hM
  have hzero : ∀ᶠ ε : ℝ in 𝓝 0,
      singleTransmission hm hv (ε,-K ε)=singleTransmission hm hv (0,-K 0) := by
    rw [hbase]
    exact single_ground_root_near hm hc hn hM hv hvc hvcomp
  have hrel := scalar_root_variation (singleTransmission_analytic hm hv (0,-K 0)).differentiableAt
    hK.neg hzero hq hcp
  have hcpos : 0<c := by
    dsimp only [c]
    rw [hk]
    exact mul_pos (by norm_num) (groundTransmission_scale_positive G hM)
  have hb : b= -groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/
      (∫ x,m x*(H1.rep G.u x)^2) := by
    have hmpos := groundTransmission_scale_positive G hM
    rw [groundJost_weighted_product G hM he] at hmpos
    have hden : (∫ x,m x*(H1.rep G.u x)^2)≠0 := by
      intro hz
      rw [hz,zero_div] at hmpos
      exact lt_irrefl 0 hmpos
    have hbq : b=q/c := by
      apply (eq_div_iff hcpos.ne').mpr
      linarith
    rw [hbq]
    dsimp only [q,c]
    rw [hk,groundJost_weighted_product G hM he,groundJost_weighted_product G hM he]
    field_simp [(groundLeftAmplitude_positive G hM).ne',hden]

  rw [← hb]
  exact hK

end
end «2610.05164v2».LocalObstruction
