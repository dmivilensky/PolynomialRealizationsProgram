import jacobi.GelfandLevitan.QuasiGaugeConvergence

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The quasi-derivative system is closed under uniform convergence of
its diagonal, solution and inhomogeneous coefficient. Its genuine
quasi-derivatives converge as a conclusion, using the independently
proved positive-strip reconstruction. Both limiting derivatives are
then obtained from the actual physical integral equations and FTC.
Use: quasiSystem_limit recovers both limiting actual derivatives from their independently established physical integral equations.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- An exact physical primitive identity gives the genuine derivative of the original strip function.
Use: quasiSystem_limit recovers both limiting actual derivatives from their independently established physical integral equations.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the fundamental theorem of calculus.
Proof: the primitive has its true endpoint derivative. The given original integral identity differs from the actual function by a constant, whose derivative is zero. -/
theorem stripDerivative_of_primitive {p q : ℝ} (hpq : p≤q) (f g : C(ClosedStrip p q,ℂ))
    (h : stripPrimitive hpq g=f-ContinuousMap.const _ (f ⟨p,⟨le_rfl,hpq⟩⟩))
    (t : ClosedStrip p q) :
    HasDerivWithinAt (stripExtension hpq f) (g t) (Icc p q) (t:ℝ) := by
  have hD := (stripPrimitive_hasDerivWithinAt hpq g t).add_const (f ⟨p,⟨le_rfl,hpq⟩⟩)
  convert hD using 1
  ext x
  change f (Set.projIcc p q hpq x)=stripPrimitive hpq g (Set.projIcc p q hpq x)+f ⟨p,⟨le_rfl,hpq⟩⟩
  rw [h]
  simp only [ContinuousMap.sub_apply,ContinuousMap.const_apply,sub_add_cancel]

/-- Actual physical quasi-derivatives converge and their true first-order equations pass to the original limit solely from uniform convergence of the original solutions and diagonal data.
Use: the original finite GL approximations discharge this theorem's genuine finite derivative assumptions and yield the actual infinite transformed ODE, without a separately postulated derivative-limit certificate.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: integrating factors and the fundamental theorem of calculus for continuous first-order systems.
Proof: reconstruct each actual finite quasi-derivative from its original first-component data. The proved norm continuity of that reconstruction gives its genuine limit. Both actual finite systems integrate to their true physical-strip primitives. Bounded integration and norm-continuous products pass both identities to the limit, and the actual FTC recovers both genuine limiting derivatives. -/
theorem quasiSystem_limit {p q : ℝ} (hpq : p<q) {ι : Type*} {l : Filter ι} [NeBot l]
    {wn : ι→C(ClosedStrip p q,ℝ)} {bn fn vn : ι→C(ClosedStrip p q,ℂ)}
    {w : C(ClosedStrip p q,ℝ)} {b f : C(ClosedStrip p q,ℂ)}
    (hw : Tendsto wn l (𝓝 w)) (hb : Tendsto bn l (𝓝 b)) (hf : Tendsto fn l (𝓝 f))
    (hD : ∀ᶠ n in l,
      (∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le (fn n))
        (2*(wn n t:ℂ)*fn n t+vn n t) (Icc p q) (t:ℝ)) ∧
      (∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le (vn n))
        (bn n t*fn n t-2*(wn n t:ℂ)*vn n t) (Icc p q) (t:ℝ))) :
    ∃ v : C(ClosedStrip p q,ℂ),Tendsto vn l (𝓝 v) ∧
      (∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le f)
        (2*(w t:ℂ)*f t+v t) (Icc p q) (t:ℝ)) ∧
      (∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le v)
        (b t*f t-2*(w t:ℂ)*v t) (Icc p q) (t:ℝ)) := by
  -- The true finite derivative limit is proved from the original solution values, before either limiting derivative is asserted.
  let v := quasiGaugeReconstruction hpq.le w b f
  have hRec : ∀ᶠ n in l,vn n=quasiGaugeReconstruction hpq.le (wn n) (bn n) (fn n) := by
    filter_upwards [hD] with n hn
    exact quasiGauge_reconstruction hpq (wn n) (bn n) (fn n) (vn n) hn.1 hn.2
  have hv : Tendsto vn l (𝓝 v) :=
    (quasiGaugeReconstruction_tendsto hpq hw hb hf).congr' (hRec.mono (fun _ hn => hn.symm))
  have hwc := ((stripComplex (p := p) (q := q)).continuous.tendsto w).comp hw
  have hfirst : Tendsto (fun n =>
      stripPrimitive hpq.le (ContinuousMap.const _ (2:ℂ)*stripComplex (wn n)*fn n+vn n)) l
      (𝓝 (stripPrimitive hpq.le (ContinuousMap.const _ (2:ℂ)*stripComplex w*f+v))) :=
    ((stripPrimitive hpq.le).continuous.tendsto _).comp (((tendsto_const_nhds.mul hwc).mul hf).add hv)
  have hfirstR : Tendsto (fun n => fn n-ContinuousMap.const _ (fn n ⟨p,⟨le_rfl,hpq.le⟩⟩)) l
      (𝓝 (f-ContinuousMap.const _ (f ⟨p,⟨le_rfl,hpq.le⟩⟩))) :=
    hf.sub (((ContinuousLinearMap.const ℝ (ClosedStrip p q)).continuous.tendsto _).comp
      (((continuous_eval_const (⟨p,⟨le_rfl,hpq.le⟩⟩:ClosedStrip p q)).tendsto _).comp hf))
  have hsecond : Tendsto (fun n =>
      stripPrimitive hpq.le (bn n*fn n-ContinuousMap.const _ (2:ℂ)*stripComplex (wn n)*vn n)) l
      (𝓝 (stripPrimitive hpq.le (b*f-ContinuousMap.const _ (2:ℂ)*stripComplex w*v))) :=
    ((stripPrimitive hpq.le).continuous.tendsto _).comp ((hb.mul hf).sub ((tendsto_const_nhds.mul hwc).mul hv))
  have hsecondR : Tendsto (fun n => vn n-ContinuousMap.const _ (vn n ⟨p,⟨le_rfl,hpq.le⟩⟩)) l
      (𝓝 (v-ContinuousMap.const _ (v ⟨p,⟨le_rfl,hpq.le⟩⟩))) :=
    hv.sub (((ContinuousLinearMap.const ℝ (ClosedStrip p q)).continuous.tendsto _).comp
      (((continuous_eval_const (⟨p,⟨le_rfl,hpq.le⟩⟩:ClosedStrip p q)).tendsto _).comp hv))
  have he1 : stripPrimitive hpq.le (ContinuousMap.const _ (2:ℂ)*stripComplex w*f+v)=
      f-ContinuousMap.const _ (f ⟨p,⟨le_rfl,hpq.le⟩⟩) := by
    apply tendsto_nhds_unique hfirst
    apply hfirstR.congr'
    filter_upwards [hD] with n hn
    exact (stripPrimitive_eq_sub hpq (fn n) _ hn.1).symm
  have he2 : stripPrimitive hpq.le (b*f-ContinuousMap.const _ (2:ℂ)*stripComplex w*v)=
      v-ContinuousMap.const _ (v ⟨p,⟨le_rfl,hpq.le⟩⟩) := by
    apply tendsto_nhds_unique hsecond
    apply hsecondR.congr'
    filter_upwards [hD] with n hn
    exact (stripPrimitive_eq_sub hpq (vn n) _ hn.2).symm
  exact ⟨v,hv,stripDerivative_of_primitive hpq.le f _ he1,stripDerivative_of_primitive hpq.le v _ he2⟩

end
end jacobi.GelfandLevitan
