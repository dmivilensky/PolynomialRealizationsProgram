import jacobi.GelfandLevitan.FiniteStripSystem

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The genuine original finite diagonal and transformed solution limits
hold in the uniform norm on every positive strip. Their actual
first-order coefficients converge in the same norm. These original
data discharge the limit hypotheses of quasiSystem_limit.
Use: the finite original diagonal limit supplies this exact coefficient to the genuine transformed quasi-derivative system.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original GL diagonal on a fixed positive physical strip.
Use: the finite original diagonal limit supplies this exact coefficient to the genuine transformed quasi-derivative system.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def transformedDiagonalStrip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) : C(ClosedStrip d (1/2),ℝ) :=
  (kernelDiagonal a ha).comp (derivativeStripInclusion hd)

/-- The actual original transformed solution on a fixed positive physical strip.
Use: finiteSolutionStrip_tendsto identifies its actual uniform-norm limit before the genuine limiting derivatives are obtained.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def transformedSolutionStrip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (z : ℂ) : C(ClosedStrip d (1/2),ℂ) :=
  ⟨fun t => transformedSolution a ha (derivativeStripInclusion hd t) z,
    (transformedSolution_continuous a ha z).comp (derivativeStripInclusion hd).continuous⟩

/-- The actual original quasi-derivative, formed from the independently proved genuine original transformed slope and actual diagonal.
Use: the limiting first-order equation identifies this same original quasi-derivative; its independently recovered derivative gives the original transformed ODE.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def transformedQuasiStrip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (z : ℂ) : C(ClosedStrip d (1/2),ℂ) :=
  transformedSlopeRows ha hd z-ContinuousMap.const _ (2:ℂ)*
    stripComplex (transformedDiagonalStrip a ha hd)*transformedSolutionStrip a ha hd z

/-- The original physical half clamp agrees with the unchanged positive-strip inclusion.
Use: both actual finite strip limits retain exactly the original physical GL endpoint.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the positive physical point already lies in the original half interval, so its clipping projection fixes it. -/
theorem halfParameterClamp_strip {d : ℝ} (hd : 0<d) (t : ClosedStrip d (1/2)) :
    halfParameterClamp (t:ℝ)=derivativeStripInclusion hd t :=
  Set.projIcc_of_mem (by norm_num) ⟨(hd.trans_le t.property.1).le,t.property.2⟩

/-- The genuine original finite diagonals converge in uniform norm to the actual original diagonal on every positive physical strip.
Use: quasiSystem_limit receives its true original diagonal coefficient limit without a separately supplied continuity or approximation certificate.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: restrict the already proved full physical-half uniform limit. The independently proved eventual original strip values remove every finite continuity totalization. The community compact-domain equivalence identifies this with the actual continuous-function norm limit. -/
theorem finiteDiagonalStrip_tendsto (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) :
    Tendsto (fun N => finiteDiagonalStrip a ha N d) atTop (𝓝 (transformedDiagonalStrip a ha hd)) := by
  -- The physical coordinate is unchanged; only the domain is restricted to its original positive strip.
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  have he : (fun N t => finiteKernelDiagonal a ha N (derivativeStripInclusion hd t))=ᶠ[atTop]
      (fun N t => finiteDiagonalStrip a ha N d t) := by
    filter_upwards [finiteStripData_values a ha hd] with N hN
    funext t
    exact ((hN 0 t).1.trans (congrArg (finiteKernelDiagonal a ha N) (halfParameterClamp_strip hd t))).symm
  exact (tendstoUniformly_congr he).mp ((finiteKernelDiagonal_uniform_limit a ha).comp (derivativeStripInclusion hd))

/-- The actual original finite transformed solutions converge in the positive-strip uniform norm to the same original u at every complex energy.
Use: the general quasi-system limit applies to the actual GL approximation sequence with no first-derivative convergence premise.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: restrict the independently proved original full-half uniform transformed-solution limit. The eventual true finite strip values remove every mkD fallback. The genuine compact-domain norm topology is exactly uniform convergence. -/
theorem finiteSolutionStrip_tendsto (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (z : ℂ) :
    Tendsto (fun N => finiteSolutionStrip a ha N d z) atTop (𝓝 (transformedSolutionStrip a ha hd z)) := by
  -- The limiting function is the original GL u, not a solution introduced by the limiting ODE.
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  have he : (fun N t => finiteTransformedSolution a ha N (derivativeStripInclusion hd t) z)=ᶠ[atTop]
      (fun N t => finiteSolutionStrip a ha N d z t) := by
    filter_upwards [finiteStripData_values a ha hd] with N hN
    funext t
    exact ((hN z t).2.1.trans (congrArg (fun x => finiteTransformedSolution a ha N x z) (halfParameterClamp_strip hd t))).symm
  exact (tendstoUniformly_congr he).mp ((finiteTransformedSolution_uniform_limit a ha z).comp (derivativeStripInclusion hd))

/-- The actual quasi-system coefficient converges in uniform norm whenever its original diagonal does.
Use: the genuine original finite diagonal limit discharges the final coefficient-limit hypothesis of quasiSystem_limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: complex inclusion and products are continuous in the original uniform function norm; the reference potential and energy are unchanged. -/
theorem quasiEquationCoefficient_tendsto (a : ℝ) {d : ℝ} (hd : 0<d) (z : ℂ)
    {wn : ℕ→C(ClosedStrip d (1/2),ℝ)} {w : C(ClosedStrip d (1/2),ℝ)}
    (hw : Tendsto wn atTop (𝓝 w)) :
    Tendsto (fun N => quasiEquationCoefficient a hd z (wn N)) atTop (𝓝 (quasiEquationCoefficient a hd z w)) := by
  have hc := ((stripComplex (p := d) (q := 1/2)).continuous.tendsto w).comp hw
  exact tendsto_const_nhds.sub ((tendsto_const_nhds.mul hc).mul hc)

end
end jacobi.GelfandLevitan
