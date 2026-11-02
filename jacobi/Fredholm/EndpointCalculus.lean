import jacobi.Fredholm.Continuity
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
Article: jacobi, Appendix D.4.
The genuine continuous interior derivatives extend to the asserted
one-sided derivatives at tau=1 and chi=0. In particular no ordinary shape
derivative of the polynomial weight beyond tau=1 is assumed or used.
Source: mathlib's mean-value extension theorem for one-sided derivatives.
Use: extends the true singular-quadrature shape derivatives to their physical full-support boundary.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A genuine continuous derivative on the open unit interval determines the left derivative at one.
Use: extends the true singular-quadrature shape derivatives to their physical full-support boundary.
Article: jacobi, Appendix D.4.
Proof: continuity gives the actual endpoint limits of the function and
its derivative. Apply the mean-value derivative extension theorem from
the left; the open interval is a genuine left neighborhood of one. -/
theorem derivative_at_one (F D : ℝ → ℝ)
    (hF : ContinuousOn F (Icc (0:ℝ) 1)) (hD : ContinuousOn D (Icc (0:ℝ) 1))
    (hd : ∀ u∈Ioo (0:ℝ) 1,HasDerivAt F (D u) u) : HasDerivWithinAt F (D 1) (Iic 1) 1 := by
  -- The limiting derivative is the original continuous physical response, not an artificial extension.
  have hle : 𝓝[<] (1:ℝ)≤𝓝[Icc (0:ℝ) 1] 1 :=
    le_inf inf_le_left (le_principal_iff.mpr (Icc_mem_nhdsLT (by norm_num : (0:ℝ)<1)))
  have hlim := (hD 1 (by norm_num)).tendsto.mono_left hle
  have heq : (fun u => deriv F u)=ᶠ[𝓝[<] (1:ℝ)] D := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with u hu
    exact (hd u hu).deriv
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
    ((hF 1 (by norm_num)).mono Ioo_subset_Icc_self)
    (Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1))
  exact (tendsto_congr' heq).mpr hlim

/-- A genuine continuous derivative on the open unit interval determines the right derivative at zero.
Use: gives the printed chi=0 boundary calculus without requiring negative determinant parameters.
Article: jacobi, Appendix D.4.
Proof: continuity supplies the endpoint limits; the actual interior
derivative agrees eventually with its continuous response. Apply the
mean-value derivative extension theorem from the right. -/
theorem derivative_at_zero (F D : ℝ → ℝ)
    (hF : ContinuousOn F (Icc (0:ℝ) 1)) (hD : ContinuousOn D (Icc (0:ℝ) 1))
    (hd : ∀ u∈Ioo (0:ℝ) 1,HasDerivAt F (D u) u) : HasDerivWithinAt F (D 0) (Ici 0) 0 := by
  -- Work only on the physical nonnegative side of the determinant parameter.
  have hle : 𝓝[>] (0:ℝ)≤𝓝[Icc (0:ℝ) 1] 0 :=
    le_inf inf_le_left (le_principal_iff.mpr (Icc_mem_nhdsGT (by norm_num : (0:ℝ)<1)))
  have hlim := (hD 0 (by norm_num)).tendsto.mono_left hle
  have heq : (fun u => deriv F u)=ᶠ[𝓝[>] (0:ℝ)] D := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with u hu
    exact (hd u hu).deriv
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
    ((hF 0 (by norm_num)).mono Ioo_subset_Icc_self)
    (Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1))
  exact (tendsto_congr' heq).mpr hlim

/-- Both actual state quadratures have their precise physical one-sided shape and determinant derivatives.
Use: completes the endpoint derivative assertions underlying the printed C1 mass and energy formulas.
Article: jacobi, Appendix D.4.
Proof: joint dominated continuity gives closed-interval continuity of
the original moments and all response moments. Restrict to each parameter
line; the proved interior derivatives and mean-value extension theorems
then give all four physical one-sided derivatives with their exact values. -/
theorem physical_endpoint_calculus {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun u => i2 u c) (shape2 1 c) (Iic 1) 1 ∧
      HasDerivWithinAt (fun u => i3 u c) (shape3 1 c) (Iic 1) 1 ∧
      HasDerivWithinAt (fun u => i2 t u) (-(t/2)*response2 t 0) (Ici 0) 0 ∧
      HasDerivWithinAt (fun u => i3 t u) (-(t/2)*response3 t 0) (Ici 0) 0 := by
  -- Each endpoint response is the jointly continuous original integral established by dominated convergence.
  have hT (F : (ℝ × ℝ) → ℝ) (hF : ContinuousOn F parameterBox) :
      ContinuousOn (fun u => F (u,c)) (Icc (0:ℝ) 1) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hu => ⟨hu,hc⟩)
  have hC (F : (ℝ × ℝ) → ℝ) (hF : ContinuousOn F parameterBox) :
      ContinuousOn (fun u => F (t,u)) (Icc (0:ℝ) 1) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨ht,hu⟩)
  have hI2 : ContinuousOn (fun p : ℝ × ℝ => i2 p.1 p.2) parameterBox := by
    simpa only [i2,one_mul] using state_integral_continuous (fun _ => 1) measurable_const (fun _ _ => by norm_num)
  have hI3 : ContinuousOn (fun p : ℝ × ℝ => i3 p.1 p.2) parameterBox :=
    state_integral_continuous (fun v => v) measurable_id (fun v hv => by rw [abs_of_pos hv.1]; exact hv.2.le)
  have hS2 : ContinuousOn (fun p : ℝ × ℝ => shape2 p.1 p.2) parameterBox := by
    simpa only [shape2,one_mul] using shape_integral_continuous (fun _ => 1) measurable_const (fun _ _ => by norm_num)
  have hS3 : ContinuousOn (fun p : ℝ × ℝ => shape3 p.1 p.2) parameterBox :=
    shape_integral_continuous (fun v => v) measurable_id (fun v hv => by rw [abs_of_pos hv.1]; exact hv.2.le)
  have hR2 : ContinuousOn (fun p : ℝ × ℝ => response2 p.1 p.2) parameterBox := by
    simpa only [response2,one_mul] using response_integral_continuous (fun _ => 1) measurable_const (fun _ _ => by norm_num)
  have hR3 : ContinuousOn (fun p : ℝ × ℝ => response3 p.1 p.2) parameterBox :=
    response_integral_continuous (fun v => v) measurable_id (fun v hv => by rw [abs_of_pos hv.1]; exact hv.2.le)
  exact ⟨derivative_at_one _ _ (hT _ hI2) (hT _ hS2) (fun u hu => (shape_calculus hu hc).1),
    derivative_at_one _ _ (hT _ hI3) (hT _ hS3) (fun u hu => (shape_calculus hu hc).2),
    derivative_at_zero _ _ (hC _ hI2) ((hC _ hR2).const_mul _) (fun u hu => (parameter_calculus ht hu).1),
    derivative_at_zero _ _ (hC _ hI3) ((hC _ hR3).const_mul _) (fun u hu => (parameter_calculus ht hu).2)⟩

end
end jacobi.Fredholm
