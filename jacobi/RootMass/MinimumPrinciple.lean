import jacobi.RootMass.SpectralNeedle
import jacobi.RootMass.Amplitude
import jacobi.RootMass.PointwisePolynomial

/-!
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
The actual minimizing density is perturbed by genuine finite-interval
replacements and normalized by its actual spectral second moment. All five
Lebesgue primitive derivatives hold on one fixed full-measure set, independent
of the replacement value. Exact right derivatives and actual admissibility
prove global pointwise minimization, rather than merely stationarity.
Source: the supplement's needle argument, with its spectral and integral remainders proved.
Use: the pointwise minimum principle and compact profile use this same genuine multiplier.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual normal multiplier determined by the complete inner amplitude derivative.
Use: the pointwise minimum principle and compact profile use this same genuine multiplier.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
-/
def normalMultiplier (m : RootDensity) (a b T : ℝ) : ℝ :=
  (3*m.energy+a*b*m.mass+b^2*m.rootIntegral)/(4*T)

/-- The actual normalized needle gives its full scalar minimizing inequality at a common Lebesgue primitive point.
Use: all derivative premises are discharged on one full-measure set in the final pointwise minimum theorem.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the actual needle has all three cost derivatives and the proved
true spectral derivative. Its fourth-root normalization is genuinely
admissible near zero. The original minimizing property gives a nonnegative
right derivative, which is exactly the stated scalar polynomial difference. -/
theorem needle_minimum_inequality {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T)
    (m : RootDensity) (hactive : observe m.toDensity .second=T) (hmin : m.cost a b=inner a b T)
    (x z : ℝ) (hz : 0≤z)
    (hm : HasDerivAt (fun v => ∫ t in x..v,m.value t) (m.value x) x)
    (hE : HasDerivAt (fun v => ∫ t in x..v,m.value t^(3/2:ℝ)) (m.value x^(3/2:ℝ)) x)
    (hR : HasDerivAt (fun v => ∫ t in x..v,sqrt (m.value t)) (sqrt (m.value x)) x)
    (hW : HasDerivAt (fun v => ∫ t in x..v,potential m.toDensity t) (potential m.toDensity x) x)
    (hmW : HasDerivAt (fun v => ∫ t in x..v,m.value t*potential m.toDensity t)
      (m.value x*potential m.toDensity x) x) :
    0≤f a b (sqrt z)-f a b (sqrt (m.value x))-
      2*normalMultiplier m a b T*potential m.toDensity x*(z-m.value x) := by
  -- Every varying function below belongs to the original actual needle density.
  let q (eps : ℝ) := m.needle z hz x eps
  let G (eps : ℝ) := observe (q eps).toDensity .second
  let E (eps : ℝ) := (q eps).energy
  let M (eps : ℝ) := (q eps).mass
  let R (eps : ℝ) := (q eps).rootIntegral
  have hGd := m.needle_spectral_derivative z hz x hm hW hmW
  have hEd := m.needle_observable_derivative z hz x (fun r => r^(3/2:ℝ)) m.energy_integrable hE
  have hMd := m.needle_observable_derivative z hz x id m.integrable hm
  have hRd := m.needle_observable_derivative z hz x sqrt m.root_integrable hR
  have hG0 : G 0=T := (observe_congr (Eventually.of_forall fun t => congrFun (m.needle_zero_value z hz x) t) .second).trans hactive
  have hE0 : E 0=m.energy := by
    change (∫ t,(m.needle z hz x 0).value t^(3/2:ℝ))=_
    rw [m.needle_zero_value]
    rfl
  have hM0 : M 0=m.mass := by
    change (∫ t,(m.needle z hz x 0).value t)=_
    rw [m.needle_zero_value]
    rfl
  have hR0 : R 0=m.rootIntegral := by
    change (∫ t,sqrt ((m.needle z hz x 0).value t))=_
    rw [m.needle_zero_value]
    rfl
  let H (eps : ℝ) := (normalization T (G eps))^3*E eps+
    (a*b/2)*(normalization T (G eps))^2*M eps+b^2*normalization T (G eps)*R eps
  have hHd := normalized_cost_derivative (G := G) (E := E) (M := M) (R := R) (a := a) (b := b) hT hG0 hGd hEd hMd hRd
  have hH0 : H 0=m.objective a b := by
    dsimp only [H]
    rw [hG0,normalization_self hT,hE0,hM0,hR0]
    norm_num only [one_pow,one_mul,mul_one]
    exact (m.objective_terms a b).symm
  -- Genuine feasibility is retained on a neighborhood of positive actual moments.
  have hGpos : ∀ᶠ eps in 𝓝[Ici (0:ℝ)] 0,0<G eps :=
    hGd.continuousWithinAt.eventually (lt_mem_nhds (by change 0<G 0; rwa [hG0]))
  have hHmin : ∀ᶠ eps in 𝓝[Ici (0:ℝ)] 0,H 0≤H eps := by
    filter_upwards [hGpos] with eps heps
    let r := normalization T (G eps)
    have hr : 0≤r := sqrt_nonneg _
    let w := (q eps).scaleRoot r hr
    have hwG : observe w.toDensity .second=T := by
      change observe ((q eps).toDensity.scale (r^2) (sq_nonneg r)) .second=T
      rw [Density.scale_second]
      change (r^2)^2*G eps=T
      rw [← pow_mul]
      exact normalization_fourth hT heps
    have hlo : m.cost a b≤w.cost a b := by rw [hmin]; exact sInf_le ⟨w,hwG.ge,rfl⟩
    have ho : m.objective a b≤w.objective a b :=
      (ENNReal.ofReal_le_ofReal_iff (w.objective_nonneg ha hb.le)).mp hlo
    rw [hH0]
    change _≤r^3*E eps+(a*b/2)*r^2*M eps+b^2*r*R eps
    rw [← (q eps).scaleRoot_objective a b r hr]
    exact ho
  have hderiv := right_derivative_nonneg hHd hHmin
  rw [hE0,hM0,hR0,rpow_div_two_eq_sqrt 3 hz,rpow_ofNat,
    rpow_div_two_eq_sqrt 3 (m.nonneg x),rpow_ofNat] at hderiv
  convert hderiv using 1
  unfold f normalMultiplier
  rw [sq_sqrt hz,sq_sqrt (m.nonneg x)]
  simp only [id_eq]
  ring

/-- Every actual inner minimizer satisfies the full global pointwise minimum principle with a proved strictly positive multiplier.
Use: constructs the compact profile and its switching boundary without assuming smooth KKT or a prescribed density shape.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: all five original primitive derivatives hold on a common full-measure
set. The proved actual normalized needle inequality holds there for every
nonnegative replacement value. This is the full global scalar minimizing
property. A nonpositive multiplier would force the density to vanish,
contradicting the actual positive active spectral threshold. -/
theorem pointwise_minimum {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T)
    (m : RootDensity) (hmin : m.cost a b=inner a b T) (hG : T≤observe m.toDensity .second) :
    ∃ mu : ℝ,0<mu ∧ mu=normalMultiplier m a b T ∧ ∀ᵐ x : ℝ,∀ n : ℝ,0≤n →
      h b (-a*b/2+2*mu*potential m.toDensity x) (sqrt (m.value x))≤
        h b (-a*b/2+2*mu*potential m.toDensity x) n := by
  -- The common null set is independent of the uncountably many replacement arguments.
  have hactive := inner_constraint_active ha hb hT m hG hmin
  let mu := normalMultiplier m a b T
  have hP : ∀ᵐ x : ℝ,∀ n : ℝ,0≤n →
      h b (-a*b/2+2*mu*potential m.toDensity x) (sqrt (m.value x))≤
        h b (-a*b/2+2*mu*potential m.toDensity x) n := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral m.integrable.locallyIntegrable,
      _root_.LocallyIntegrable.ae_hasDerivAt_integral m.energy_integrable.locallyIntegrable,
      _root_.LocallyIntegrable.ae_hasDerivAt_integral m.root_integrable.locallyIntegrable,
      _root_.LocallyIntegrable.ae_hasDerivAt_integral ((potential_continuous m.toDensity).1.locallyIntegrable (μ := volume)),
      _root_.LocallyIntegrable.ae_hasDerivAt_integral m.potential_product_integrable.locallyIntegrable] with x hm hE hR hW hmW
    intro n hn
    have hi := needle_minimum_inequality ha hb hT m hactive hmin x (n^2) (sq_nonneg n)
      (hm x) (hE x) (hR x) (hW x) (hmW x)
    rw [sqrt_sq hn] at hi
    have hs := sq_sqrt (m.nonneg x)
    unfold f at hi
    unfold h
    dsimp only [mu] at *
    nlinarith [congrArg (fun r : ℝ => (2*mu*potential m.toDensity x)*r) hs]
  have hmu : 0<mu := by
    by_contra! hn
    have hz : m.value=ᵐ[volume] (0 : ℝ → ℝ) := by
      filter_upwards [hP] with x hx
      have hh := hx 0 le_rfl
      have hprod : 2*mu*potential m.toDensity x*m.value x≤0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (potential_nonneg m.toDensity x)) (m.nonneg x)
      have hs := sq_sqrt (m.nonneg x)
      by_contra hne
      have hp := f_pos ha hb (sqrt_pos.mpr (lt_of_le_of_ne (m.nonneg x) (Ne.symm hne)))
      unfold h at hh
      unfold f at hp
      nlinarith [congrArg (fun r : ℝ => (2*mu*potential m.toDensity x)*r) hs]
    have hmass : m.mass=0 := by simpa only [Density.mass,Pi.zero_apply,integral_zero] using integral_congr_ae hz
    exact (mass_pos_of_observe_pos m.toDensity .second (hT.trans_le hG)).ne' hmass
  exact ⟨mu,hmu,rfl,hP⟩

end
end jacobi.RootMass
