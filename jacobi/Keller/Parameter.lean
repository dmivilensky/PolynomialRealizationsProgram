import jacobi.Keller.Quadratures

/-!
Article: jacobi, Theorem D.6.
The actual mass curve sqrt(c)*j_2(c) is continuous and strictly decreasing
from 1/2 toward 1/3. The inverse parameter converts its complete range into
an ordinary closed-interval intermediate-value theorem, giving the unique
finite c>1 for every strictly active mass bound.
Source: the proved actual quadrature continuity, strict comparison and exact endpoint primitives.
Use: transfers all proved rescaled-integral facts to the source's c>=1 domain.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every finite admissible original parameter gives an inverse parameter in the compact quadrature interval.
Use: transfers all proved rescaled-integral facts to the source's c>=1 domain.
Article: jacobi, Theorem D.6.
Proof: invert the positive lower bound c>=1. -/
theorem inverse_mem {c : ℝ} (hc : 1≤c) : c⁻¹∈Icc (0:ℝ) 1 :=
  ⟨inv_nonneg.mpr (zero_lt_one.trans_le hc).le,inv_le_one_of_one_le₀ hc⟩

/-- The source's actual normalized Keller mass curve.
Use: the active mass equation is 3*ell*massCurve(c)=M.
Article: jacobi, Theorem D.6.
-/
def massCurve (c : ℝ) : ℝ := sqrt c*j 2 c

/-- Every compact-parameter quadrature is nonnegative.
Use: strict comparison from e=0 proves positivity of every literal finite-c j_k.
Article: jacobi, Theorem D.6.
Proof: integrate the nonnegative numerator divided by a nonnegative square root on (0,1). -/
theorem J_nonneg (k : ℕ) (e : ℝ) : 0≤J k e := by
  rw [J,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hv2 : v^2<1 := by nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
  exact div_nonneg (pow_nonneg (sub_pos.mpr hv2).le _) (sqrt_nonneg _)

/-- Every printed positive-order Keller quadrature at a finite admissible shape is strictly positive.
Use: proves convergence of the computed positive root-mass integral rather than allowing a Bochner junk value.
Article: jacobi, Theorem D.6.
Proof: compare J_k(1/c) strictly with its nonnegative zero-parameter value and cancel sqrt(c)>0. -/
theorem j_pos {k : ℕ} (hk : 1≤k) {c : ℝ} (hc : 1≤c) : 0<j k c := by
  have hcp : 0<c := zero_lt_one.trans_le hc
  have hJ : 0<J k c⁻¹ := (J_nonneg k 0).trans_lt
    (J_strictMono hk (by norm_num) (inverse_mem hc) (inv_pos.mpr hcp))
  rw [← j_rescale k hcp] at hJ
  exact (mul_pos_iff_of_pos_left (sqrt_pos.mpr hcp)).mp hJ

/-- Every printed positive-order Keller quadrature is a genuine convergent interval integral.
Use: all three source state integrals are finite before they enter the optimizer evaluation.
Article: jacobi, Theorem D.6.
Proof: the proved strictly positive actual integral cannot be an undefined Bochner integral. -/
theorem j_integrable {k : ℕ} (hk : 1≤k) {c : ℝ} (hc : 1≤c) :
    IntervalIntegrable (fun v : ℝ => (1-v^2)^k/sqrt ((1-v^2/c)*(c*A v-1))) volume 0 1 :=
  intervalIntegral.intervalIntegrable_of_integral_ne_zero (j_pos hk hc).ne'

/-- All printed normalized Keller quadratures are continuous on their full admissible parameter interval.
Use: includes the source's continuity claim for every k=1,2,3, as well as the mass curve.
Article: jacobi, Theorem D.6.
Proof: compose the actual dominated integral continuity on the compact inverse-parameter interval with inversion. -/
theorem normalized_j_continuous {k : ℕ} (hk : 1≤k) :
    ContinuousOn (fun c => sqrt c*j k c) (Ici (1:ℝ)) := by
  have hinv : ContinuousOn (fun c : ℝ => c⁻¹) (Ici (1:ℝ)) :=
    fun c hc => (continuousAt_inv₀ (zero_lt_one.trans_le hc).ne').continuousWithinAt
  apply ((J_continuous hk).comp hinv (fun _ hc => inverse_mem hc)).congr
  intro c hc
  exact j_rescale k (zero_lt_one.trans_le hc)

/-- The true normalized Keller mass curve is continuous on the full c>=1 interval.
Use: supplies the source's global parameter regularity without numerical fitting or quadrature assumptions.
Article: jacobi, Theorem D.6.
Proof: compose compact-parameter dominated continuity with c↦1/c and apply the exact rescaling. -/
theorem massCurve_continuous : ContinuousOn massCurve (Ici (1:ℝ)) := by
  exact normalized_j_continuous (by decide : 1≤2)

/-- The true normalized Keller mass curve is strictly decreasing on the entire admissible interval.
Use: uniqueness and exhaustive branch selection for every mass-constrained optimizer.
Article: jacobi, Theorem D.6.
Proof: inversion reverses positive c order, while the actual compact-parameter quadrature is strictly increasing. -/
theorem massCurve_strictAnti : StrictAntiOn massCurve (Ici (1:ℝ)) := by
  intro c hc d hd hcd
  unfold massCurve
  rw [j_rescale 2 (zero_lt_one.trans_le hd),j_rescale 2 (zero_lt_one.trans_le hc)]
  exact J_strictMono (by decide : 1≤2) (inverse_mem hd) (inverse_mem hc)
    ((inv_lt_inv₀ (zero_lt_one.trans_le hd) (zero_lt_one.trans_le hc)).mpr hcd)

/-- The exact Keller mass transition is one half.
Use: the source's free-mass threshold is M=3*ell/2.
Article: jacobi, Theorem D.6.
Proof: apply the proved exact rescaling and transition primitive. -/
theorem massCurve_one : massCurve 1=1/2 := by
  rw [massCurve,j_rescale 2 zero_lt_one,inv_one,J_one_values.2.1]

/-- The actual normalized Keller mass curve tends to one third at infinity.
Use: proves its complete stated range and the limiting minimal admissible mass ell.
Article: jacobi, Theorem D.6.
Proof: 1/c tends to zero within [0,1]; compose dominated endpoint continuity with this limit and use the exact primitive at zero. -/
theorem massCurve_limit : Tendsto massCurve atTop (𝓝 (1/3:ℝ)) := by
  -- A single eventual c>=1 condition licenses the exact original-parameter identity and compact domain.
  have hi : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝[Icc (0:ℝ) 1] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero,
      (eventually_ge_atTop (1:ℝ)).mono fun _ hc => inverse_mem hc⟩
  have hh := ((J_continuous (by decide : 1≤2)) 0 (by norm_num)).tendsto.comp hi
  rw [J_two_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with c hc
  exact (j_rescale 2 (zero_lt_one.trans_le hc)).symm

/-- The actual c>1 mass curve lies strictly between its two exact endpoint values.
Use: rules out the active-mass branch when M>=3*ell/2.
Article: jacobi, Theorem D.6.
Proof: compare J_2(1/c) with J_2(0), and compare the original c with the transition c=1. -/
theorem massCurve_bounds {c : ℝ} (hc : 1<c) : (1/3:ℝ)<massCurve c ∧ massCurve c<1/2 := by
  constructor
  · rw [massCurve,j_rescale 2 (zero_lt_one.trans hc),← J_two_zero]
    exact J_strictMono (by decide : 1≤2) (by norm_num) (inverse_mem hc.le)
      (inv_pos.mpr (zero_lt_one.trans hc))
  · rw [← massCurve_one]
    exact massCurve_strictAnti (by simp) hc.le hc

/-- Every strictly active Keller mass bound determines one and only one finite shape c>1.
Use: the exact constrained minimum refers to a genuinely existing unique root of the printed mass equation.
Article: jacobi, Theorem D.6.
Proof: use the actual continuous J_2 on [0,1] and its exact endpoint values.
The strict mass inequalities put the target in the interior. Invert its
positive interior parameter; strict decrease of the original mass curve proves uniqueness. -/
theorem mass_parameter_exists_unique {ell M : ℝ} (hell : 0<ell) (hlo : ell<M) (hhi : M<3*ell/2) :
    ∃ c : ℝ,1<c ∧ 3*ell*massCurve c=M ∧ ∀ d : ℝ,1<d → 3*ell*massCurve d=M → d=c := by
  -- No limiting or numerical root certificate is assumed.
  let r := M/(3*ell)
  have hr0 : J 2 0<r := by rw [J_two_zero]; dsimp only [r]; apply (lt_div_iff₀ (by positivity)).mpr; linarith
  have hr1 : r<J 2 1 := by rw [J_one_values.2.1]; dsimp only [r]; apply (div_lt_iff₀ (by positivity)).mpr; linarith
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1)
    (J_continuous (by decide : 1≤2)) ⟨hr0.le,hr1.le⟩
  have he0 : 0<e := by
    apply lt_of_le_of_ne he.1
    intro hz
    rw [← hz] at heq
    exact hr0.ne heq
  have he1 : e<1 := by
    apply lt_of_le_of_ne he.2
    intro hz
    rw [hz] at heq
    exact hr1.ne' heq
  let c := e⁻¹
  have hce : c*e=1 := inv_mul_cancel₀ he0.ne'
  have hc : 1<c := by dsimp only [c]; nlinarith [inv_pos.mpr he0]
  have hroot : 3*ell*massCurve c=M := by
    rw [massCurve,j_rescale 2 (zero_lt_one.trans hc)]
    simp only [c,inv_inv]
    rw [heq]
    dsimp only [r]
    field_simp
  refine ⟨c,hc,hroot,fun d hd hde => ?_⟩
  apply massCurve_strictAnti.injOn hd.le hc.le
  nlinarith [hroot,hde]

end
end jacobi.Keller
