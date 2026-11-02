import jacobi.GelfandLevitan.QuasiSystemLimit

/-!
Article: jacobi, Theorem 2.1.
The actual finite GL diagonals, solutions and quasi-derivatives are
continuous on every fixed positive physical strip for all sufficiently
long spectral prefixes. The community mkD only totalizes the finitely
many earlier prefixes; every eventual value is proved to be the
unchanged original finite GL value.
Use: quasiEquationCoefficient forms the actual first-order transformed quasi-derivative system coefficient.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The reference potential on a fixed nonsingular physical strip.
Use: quasiEquationCoefficient forms the actual first-order transformed quasi-derivative system coefficient.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def stripPotential (a : ℝ) {d : ℝ} (hd : 0<d) : C(ClosedStrip d (1/2),ℝ) :=
  ⟨fun t => potential a t,by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : (t:ℝ)∈Ioo (0:ℝ) 1 := ⟨hd.trans_le t.property.1,by linarith [t.property.2]⟩
    exact (((potential_continuousOn a) (t:ℝ) ht).continuousAt
      (Ioo_mem_nhds ht.1 ht.2)).comp_of_eq continuous_subtype_val.continuousAt rfl⟩

/-- The actual coefficient in the first-order transformed quasi-derivative system.
Use: finiteStripSystem and the actual uniform-norm limit use v'=(q-z-4*w^2)*u-2*w*v.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def quasiEquationCoefficient (a : ℝ) {d : ℝ} (hd : 0<d) (z : ℂ)
    (w : C(ClosedStrip d (1/2),ℝ)) : C(ClosedStrip d (1/2),ℂ) :=
  stripComplex (stripPotential a hd)-ContinuousMap.const _ z-
    ContinuousMap.const _ (4:ℂ)*stripComplex w*stripComplex w

/-- The actual finite GL diagonal as a positive-strip continuous function beyond the proved common spectral threshold.
Use: finiteStripData_values proves every eventual value is the original finite diagonal, and its genuine original uniform limit supplies the transformed ODE coefficient.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: mathlib ContinuousMap.mkD totalization; the fallback affects only prefixes outside the proved eventual continuity range. -/
def finiteDiagonalStrip (a : ℝ) (ha : -1<a) (N : ℕ) (d : ℝ) : C(ClosedStrip d (1/2),ℝ) :=
  ContinuousMap.mkD (fun t => finiteKernelDiagonal a ha N (halfParameterClamp (t:ℝ))) 0

/-- The actual finite transformed solution as a continuous function on the physical positive strip beyond the proved common spectral threshold.
Use: finiteStripData_values retains the original finite GL solution and its uniform limit in quasiSystem_limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: mathlib ContinuousMap.mkD, with its genuine eventual source-value equality proved below. -/
def finiteSolutionStrip (a : ℝ) (ha : -1<a) (N : ℕ) (d : ℝ) (z : ℂ) : C(ClosedStrip d (1/2),ℂ) :=
  ContinuousMap.mkD (fun t => finiteTransformedSolution a ha N (halfParameterClamp (t:ℝ)) z) 0

/-- The actual finite transformed quasi-derivative on a fixed positive physical strip beyond the proved common spectral threshold.
Use: finiteStripSystem proves its genuine first-order equations, and quasiSystem_limit proves its actual uniform-norm convergence as a conclusion.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: mathlib ContinuousMap.mkD, with the fallback removed from every eventual source identity below. -/
def finiteQuasiStrip (a : ℝ) (ha : -1<a) (N : ℕ) (d : ℝ) (z : ℂ) : C(ClosedStrip d (1/2),ℂ) :=
  ContinuousMap.mkD (fun t => finiteTransformedQuasiDerivative a ha N z (t:ℝ)) 0

/-- The actual original finite diagonal, solution and quasi-derivative are continuous on every fixed positive physical strip beyond one original spectral threshold.
Use: finiteStripData_values removes every mkD fallback from the genuine approximation sequence, and finiteStripSystem retains the original true derivatives.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the independently proved genuine finite diagonal, solution and quasi-derivative derivatives imply continuity within the original physical strip. The local half-point derivative strips are genuine neighborhoods within the same fixed strip, including its midpoint endpoint. -/
theorem finiteStripData_continuous (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) :
    ∀ᶠ N : ℕ in atTop,∀ z : ℂ,
      Continuous (fun t : ClosedStrip d (1/2) => finiteKernelDiagonal a ha N (halfParameterClamp (t:ℝ))) ∧
      Continuous (fun t : ClosedStrip d (1/2) => finiteTransformedSolution a ha N (halfParameterClamp (t:ℝ)) z) ∧
      Continuous (fun t : ClosedStrip d (1/2) => finiteTransformedQuasiDerivative a ha N z (t:ℝ)) := by
  -- Continuity is derived for the same original functions whose genuine finite derivative identities were proved.
  filter_upwards [finiteKernelDiagonal_hasDerivWithinAt a ha,finiteTransformedSolution_hasDerivWithinAt a ha,
    finiteTransformedQuasiDerivative_hasDerivWithinAt a ha] with N hW hU hV z
  have hphys (t : ℝ) (ht : t∈Icc d (1/2)) : t∈Icc (0:ℝ) (1/2) :=
    ⟨(hd.trans_le ht.1).le,ht.2⟩
  have hwc : ContinuousOn (fun t => finiteKernelDiagonal a ha N (halfParameterClamp t)) (Icc d (1/2)) :=
    fun t ht => (hW d hd ⟨t,hphys t ht⟩ ht.1).continuousWithinAt
  have huc : ContinuousOn (fun t => finiteTransformedSolution a ha N (halfParameterClamp t) z) (Icc d (1/2)) :=
    fun t ht => (hasDerivWithinAt_physicalStrip ⟨t,hphys t ht⟩ (hd.trans_le ht.1)
      (hU ⟨t,hphys t ht⟩ z (hd.trans_le ht.1))).continuousWithinAt
  have hvc : ContinuousOn (finiteTransformedQuasiDerivative a ha N z) (Icc d (1/2)) :=
    fun t ht => (hasDerivWithinAt_physicalStrip ⟨t,hphys t ht⟩ (hd.trans_le ht.1)
      (hV ⟨t,hphys t ht⟩ z (hd.trans_le ht.1))).continuousWithinAt
  exact ⟨continuousOn_iff_continuous_domRestrict.mp hwc,continuousOn_iff_continuous_domRestrict.mp huc,
    continuousOn_iff_continuous_domRestrict.mp hvc⟩

/-- Every sufficiently long continuous strip approximation has exactly its original finite GL values at every actual physical point.
Use: the true finite system and the already proved original diagonal/solution uniform limits are transferred to the same actual strip functions.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original finite functions are eventually continuous by their proved actual derivatives. The community mkD value theorem therefore removes all three totalization fallbacks at every physical point. -/
theorem finiteStripData_values (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) :
    ∀ᶠ N : ℕ in atTop,∀ (z : ℂ) (t : ClosedStrip d (1/2)),
      finiteDiagonalStrip a ha N d t=finiteKernelDiagonal a ha N (halfParameterClamp (t:ℝ)) ∧
      finiteSolutionStrip a ha N d z t=finiteTransformedSolution a ha N (halfParameterClamp (t:ℝ)) z ∧
      finiteQuasiStrip a ha N d z t=finiteTransformedQuasiDerivative a ha N z (t:ℝ) := by
  filter_upwards [finiteStripData_continuous a ha hd] with N hN z t
  exact ⟨ContinuousMap.mkD_apply_of_continuous (hN z).1,
    ContinuousMap.mkD_apply_of_continuous (hN z).2.1,ContinuousMap.mkD_apply_of_continuous (hN z).2.2⟩

end
end jacobi.GelfandLevitan
