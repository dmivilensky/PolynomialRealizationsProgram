import jacobi.GelfandLevitan.QuasiGaugeReconstruction

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The quasi-derivative reconstructed from actual solution values and
diagonals is continuous in the uniform norm. Together with the proved
exact reconstruction gives the actual finite derivative limit,
rather than assuming it as a separate analytic certificate.
Use: the already proved finite GL solution and diagonal limits then give the actual finite quasi-derivative limit, without any assumption about convergence of finite diagonal derivatives or initial slopes.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine physical-strip quasi-derivative reconstruction preserves uniform-norm limits of the original diagonal, solution and inhomogeneous coefficient.
Use: the already proved finite GL solution and diagonal limits then give the actual finite quasi-derivative limit, without any assumption about convergence of finite diagonal derivatives or initial slopes.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine integrating factors, bounded original primitives, products and endpoint evaluations are continuous in the actual uniform norms. The true limiting denominator is strictly positive by its original physical integral formula. Thus the recovered actual initial value and the same original reconstructed quasi-derivative converge in norm. -/
theorem quasiGaugeReconstruction_tendsto {p q : ℝ} (hpq : p<q) {ι : Type*} {l : Filter ι}
    {wn : ι→C(ClosedStrip p q,ℝ)} {bn fn : ι→C(ClosedStrip p q,ℂ)}
    {w : C(ClosedStrip p q,ℝ)} {b f : C(ClosedStrip p q,ℂ)}
    (hw : Tendsto wn l (𝓝 w)) (hb : Tendsto bn l (𝓝 b)) (hf : Tendsto fn l (𝓝 f)) :
    Tendsto (fun n => quasiGaugeReconstruction hpq.le (wn n) (bn n) (fn n)) l
      (𝓝 (quasiGaugeReconstruction hpq.le w b f)) := by
  -- Every limit is in the original uniform function norm; the only division uses the independently proved positive physical denominator.
  have hg : Tendsto (fun n => stripGauge hpq.le 2 (wn n)) l (𝓝 (stripGauge hpq.le 2 w)) :=
    ((stripGauge_continuous hpq.le 2).tendsto w).comp hw
  have hh : Tendsto (fun n => stripGauge hpq.le (-2) (wn n)) l (𝓝 (stripGauge hpq.le (-2) w)) :=
    ((stripGauge_continuous hpq.le (-2)).tendsto w).comp hw
  have hgc := ((stripComplex (p := p) (q := q)).continuous.tendsto (stripGauge hpq.le 2 w)).comp hg
  have hhc := ((stripComplex (p := p) (q := q)).continuous.tendsto (stripGauge hpq.le (-2) w)).comp hh
  have hH : Tendsto (fun n => quasiGaugePrimitive hpq.le (wn n) (bn n) (fn n)) l
      (𝓝 (quasiGaugePrimitive hpq.le w b f)) :=
    ((stripPrimitive hpq.le).continuous.tendsto _).comp ((hgc.mul hb).mul hf)
  have hR : Tendsto (fun n => quasiGaugeRemainder hpq.le (wn n) (bn n) (fn n)) l
      (𝓝 (quasiGaugeRemainder hpq.le w b f)) :=
    ((stripPrimitive hpq.le).continuous.tendsto _).comp ((hhc.mul hhc).mul hH)
  have hD : Tendsto (fun n => quasiGaugeDenominator hpq.le (wn n)) l
      (𝓝 (quasiGaugeDenominator hpq.le w)) :=
    (continuous_eval_const (⟨q,⟨hpq.le,le_rfl⟩⟩:ClosedStrip p q)).tendsto _ |>.comp
      (((stripPrimitive hpq.le).continuous.tendsto _).comp (hh.mul hh))
  have hnum := (((continuous_eval_const (⟨q,⟨hpq.le,le_rfl⟩⟩:ClosedStrip p q)).tendsto _).comp hf).mul
    (((continuous_eval_const (⟨q,⟨hpq.le,le_rfl⟩⟩:ClosedStrip p q)).tendsto _).comp hhc)
  have hinit : Tendsto (fun n => quasiGaugeInitial hpq.le (wn n) (bn n) (fn n)) l
      (𝓝 (quasiGaugeInitial hpq.le w b f)) :=
    ((hnum.sub (((continuous_eval_const (⟨p,⟨le_rfl,hpq.le⟩⟩:ClosedStrip p q)).tendsto _).comp hf)).sub
      (((continuous_eval_const (⟨q,⟨hpq.le,le_rfl⟩⟩:ClosedStrip p q)).tendsto _).comp hR)).div
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hD)
      (Complex.ofReal_ne_zero.mpr (quasiGaugeDenominator_pos hpq w).ne')
  exact hhc.mul ((((ContinuousLinearMap.const ℝ (ClosedStrip p q)).continuous.tendsto _).comp hinit).add hH)

end
end jacobi.GelfandLevitan
