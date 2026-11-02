import jacobi.Fredholm.GreenQuadrature
import jacobi.Fredholm.StateIntegrals
import jacobi.Variational.GreenLogDeterminant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: jacobi, Theorem D.7.
The actual spatial determinant is integrated over the entire genuine Green
branch. Splitting at the switching value gives the elementary logarithmic
free tail and the normalized core integral. All integrability and splitting
hypotheses come from the proved actual determinant identity.
Source: Gel'fand--Dikii, the actual Green substitution and the integral of 1/g.
Use: computes the determinant's exact tail contribution, including a zero-length free-support tail.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The entire exterior Green phase gives the elementary reciprocal logarithmic density.
Use: computes the determinant's exact tail contribution, including a zero-length free-support tail.
Article: jacobi, Theorem D.7.
Proof: the clipped density vanishes below the switching value, so the
phase square root is the positive factor 2*g-1; rational cancellation is then legitimate. -/
theorem exterior_weight (A e v : ℝ) (hv : (1/2:ℝ)<v) (he : v≤e) :
    2*((1-(2*v)⁻¹)/sqrt (phase A e v))=v⁻¹ := by
  have hpos : 0<2*v-1 := by linarith
  have hv0 : v≠0 := ne_of_gt (by linarith)
  unfold phase
  rw [max_eq_right (sub_nonpos.mpr he)]
  norm_num only [zero_pow (by decide : 3≠0),mul_zero,sub_zero]
  rw [sqrt_sq hpos.le]
  field_simp [hpos.ne',hv0]

/-- The actual normalized core Green weight has precisely the printed Fredholm integrand.
Use: evaluates the non-elementary core contribution in the determinant quadrature.
Article: jacobi, Theorem D.7.
Proof: substitute the exact affine Green factors and normalized phase.
The upper turning excess is positive, so its square root has the stated
sign. All remaining cancellations use proved positive parameter denominators. -/
theorem core_weight {t c v : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) :
    2*delta t c*((1-(2*(jacobi.Fredholm.edge t c+delta t c*v))⁻¹)/
      sqrt (phase (amplitude t c) (jacobi.Fredholm.edge t c)
        (jacobi.Fredholm.edge t c+delta t c*v)))=t*c*determinantWeight t c v := by
  -- The same common P controls both the true Green phase and the printed denominator.
  have hden : 0<1-c := sub_pos.mpr hc.2
  have hp : 0<2*peak c-1 := by
    have hh : 2*peak c-1=c/(1-c) := by unfold peak; field_simp; ring
    rw [hh]
    exact div_pos hc.1 hden
  have hN := nu_bounds ⟨ht.1.le,ht.2⟩ ⟨hc.1.le,hc.2⟩ ⟨hv.1.le,hv.2.le⟩
  have hNp : 0<nu t c v := hN.1.trans_le hN.2.1
  have hS := sqrt_pos.mpr (P_pos ⟨ht.1.le,ht.2⟩ ⟨hc.1.le,hc.2.le⟩ hv)
  rw [phase_affine ht hc hv.1.le,sqrt_mul (sq_nonneg _),sqrt_sq hp.le]
  rw [(affine_coordinate hc.2.ne v).1]
  unfold determinantWeight delta peak
  field_simp [hden.ne',hNp.ne',hS.ne',hc.1.ne']
  unfold nu L
  ring

/-- The original attained optimizer has the exact printed regularized Fredholm quadrature.
Use: its active spectral threshold becomes determinant(tau,chi)=d in the exact minimum theorem.
Article: jacobi, Theorem D.7.
Proof: use the actual convergent Green determinant integral and the
genuine whole-tail substitution. Split its integrable phase weight at g_e.
The exterior is the reciprocal logarithmic integral; the affine change
of variables in the core gives the printed normalized weight. Finally
subtract the already proved actual trace s*mass. -/
theorem Optimizer.determinant_quadrature {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    P.density.fredholmReal s=determinant (P.tau hs) (P.chi hs) := by
  -- Every interval split is justified by the original actual determinant's convergence.
  let H := fun v : ℝ => 1-(2*v)⁻¹
  let W := fun v : ℝ => H v/sqrt (phase P.A P.edge v)
  have hg := (P.shape hs).1
  have he := (P.parameter_signs hs).1
  have hHp := (P.density.green_log_determinant P.continuous hs.le P.pole).2.1
  have hH : Integrable (fun x => H (P.g hs.le x)) := hHp
  obtain ⟨hWi,hquad⟩ := P.green_quadrature hs H hH
  have htail : IntervalIntegrable W volume (1/2:ℝ) P.edge :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le he).mpr
      (hWi.mono_set fun _ hx => ⟨hx.1,hx.2.trans hg⟩)
  have hcore : IntervalIntegrable W volume P.edge (P.g hs.le 0) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hg.le).mpr
      (hWi.mono_set fun _ hx => ⟨he.trans_lt hx.1,hx.2⟩)
  have htail_eval : 2*(∫ v in (1/2:ℝ)..P.edge,W v)=log (2*P.edge) := by
    rw [← intervalIntegral.integral_const_mul]
    have hsame : (∫ v in (1/2:ℝ)..P.edge,2*W v)=∫ v in (1/2:ℝ)..P.edge,v⁻¹ := by
      rw [intervalIntegral.integral_of_le he,intervalIntegral.integral_of_le he,
        integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
      exact setIntegral_congr_fun measurableSet_Ioo fun v hv => exterior_weight P.A P.edge v hv.1 hv.2.le
    rw [hsame,integral_inv_of_pos (by norm_num) (by linarith : 0<P.edge)]
    congr 1
    ring
  have hparams := P.parameters hs
  have hinv := P.inverse_parameters hs
  have hgap : 0<P.g hs.le 0-P.edge := sub_pos.mpr hg
  have haff := intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := 1) W
    (P.g hs.le 0-P.edge) P.edge
  simp only [smul_eq_mul,mul_zero,add_zero,mul_one,add_sub_cancel] at haff
  have hcore_eval : 2*(∫ v in P.edge..P.g hs.le 0,W v)=P.tau hs*P.chi hs*
      (∫ v in (0:ℝ)..1,determinantWeight (P.tau hs) (P.chi hs) v) := by
    rw [← haff,← mul_assoc,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v hv
    have hh := core_weight hparams.1 hparams.2 hv
    rw [P.amplitude_eq hs,hinv.2.1,hinv.2.2] at hh
    exact hh
  have hD := (P.density.fredholm_spatial_integral P.continuous hs.le P.pole).2.1
  have hsubtract : P.density.fredholmReal s=(∫ x,H (P.g hs.le x))-s*P.density.mass := by
    rw [hD,Density.mass,← integral_const_mul,← integral_sub hH (P.density.integrable.const_mul s)]
    rfl
  rw [hsubtract,hquad,← intervalIntegral.integral_add_adjacent_intervals htail hcore,mul_add,
    htail_eval,hcore_eval,P.mass_quadrature hs,determinant,← hinv.2.1]
  congr 2
  unfold jacobi.Fredholm.edge
  congr 1
  field_simp [sub_ne_zero.mpr hparams.2.2.ne']

end
end jacobi.Fredholm
