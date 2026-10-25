import polyak.General.QuadraticRateDefinitions
import polyak.General.QuadraticScalar
import polyak.Growth.Quadratic

/-! A dimension- and curvature-uniform bound for the actual quadratic
from-rest scalar response. The polynomial prefactor includes double roots;
no distinct-root or diagonalizability assumption is used for the recurrence. -/
noncomputable section
namespace polyak.General
open Filter Set
open scoped Topology

def quadraticEnvelope (R β : ℝ) (n : ℕ) : ℝ :=
  ((n:ℝ)+1)*R^n+β*(n:ℝ)*R^(n-1)

theorem quadraticEnvelope_nonneg {R β : ℝ} (hR : 0≤R) (hβ : 0≤β) (n : ℕ) :
    0≤quadraticEnvelope R β n := by unfold quadraticEnvelope; positivity

@[simp] theorem quadraticEnvelope_zero (R β : ℝ) : quadraticEnvelope R β 0=1 := by
  simp [quadraticEnvelope]

theorem rootRadius_curvature_le_quadraticRate {μ L α β lam : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) (hlam : lam∈Icc μ L) :
    rootRadius (1+β-α*lam) β≤Dynamics.quadraticRate μ L α β := by
  obtain ⟨z,hz,he⟩ := (rootRadius_isGreatest (p:=1+β-α*lam) hβ).1
  exact (Dynamics.quadraticRate_isGreatest hμ hL hα hβ hβ1 hquad).2
    ⟨lam,hlam,z,hz,he⟩

theorem quadraticScalar_uniform_bound {μ L α β lam : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) (hlam : lam∈Icc μ L) (n : ℕ) :
    |quadraticScalar (1+β-α*lam) β n|≤
      quadraticEnvelope (Dynamics.quadraticRate μ L α β) β n := by
  have hR := rootRadius_curvature_le_quadraticRate hμ hL hα hβ hβ1 hquad hlam
  have hR0 := rootRadius_nonneg (1+β-α*lam) β
  cases n with
  | zero => simp
  | succ n =>
    have hh := quadraticScalar_bound (p:=1+β-α*lam) hβ n
    rw [abs_of_nonneg hβ] at hh
    have hh' : ((n:ℝ)+2)*(rootRadius (1+β-α*lam) β)^(n+1)+
        β*((n:ℝ)+1)*(rootRadius (1+β-α*lam) β)^n≤
        ((n:ℝ)+2)*(Dynamics.quadraticRate μ L α β)^(n+1)+
        β*((n:ℝ)+1)*(Dynamics.quadraticRate μ L α β)^n := by gcongr
    apply hh.trans
    convert hh' using 1
    simp only [quadraticEnvelope,Nat.cast_add,Nat.cast_one,
      Nat.add_sub_cancel]
    ring

/-- The same bound, stated directly for the original scalar gradient executor. -/
theorem scalarQuadratic_uniform_bound {μ L α β lam : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) (hlam : lam∈Icc μ L) (n : ℕ) :
    |Dynamics.iterate (fun x : ℝ=>lam*x) α β 1 n|≤
      quadraticEnvelope (Dynamics.quadraticRate μ L α β) β n := by
  rw [quadraticScalar_iterate]
  exact quadraticScalar_uniform_bound hμ hL hα hβ hβ1 hquad hlam n

/-- Every strictly larger exponential absorbs the uniform polynomial factor. -/
theorem quadraticEnvelope_exponential {R β r : ℝ} (hR : 0<R) (hβ : 0≤β)
    (hr : R<r) : ∃ C : ℝ,0<C ∧ ∀ n : ℕ,quadraticEnvelope R β n≤C*r^n := by
  let q:=R/r
  have hr0 : 0<r := hR.trans hr
  have hq0 : 0≤q := (div_pos hR hr0).le
  have hq1 : q<1 := (div_lt_one hr0).mpr hr
  have hs : Summable (fun n : ℕ=>((n:ℝ)+1)*q^n) := by
    have hh : ‖q‖<1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1
    simpa only [pow_one,add_mul,one_mul] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hh).add
        (summable_geometric_of_lt_one hq0 hq1)
  let S:=∑' n : ℕ,((n:ℝ)+1)*q^n
  have hS : 1≤S := by
    simpa only [Nat.cast_zero,zero_add,pow_zero,mul_one] using
      hs.le_tsum 0 (fun n _=>by positivity)
  have hcoef : 0<1+β/R := by positivity
  refine ⟨(1+β/R)*S,mul_pos hcoef (lt_of_lt_of_le zero_lt_one hS),?_⟩
  intro n
  have hn : ((n:ℝ)+1)*q^n≤S := hs.le_tsum n (fun n _=>by positivity)
  have hbase : quadraticEnvelope R β n≤(1+β/R)*((n:ℝ)+1)*R^n := by
    cases n with
    | zero =>
      simp only [quadraticEnvelope_zero,Nat.cast_zero,zero_add,pow_zero,mul_one]
      exact le_add_of_nonneg_right (div_nonneg hβ hR.le)
    | succ n =>
      unfold quadraticEnvelope
      simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
      rw [pow_succ]
      have he : (1+β/R)*((n:ℝ)+1+1)*(R^n*R)=
          ((n:ℝ)+1+1)*(R^n*R)+β*((n:ℝ)+1+1)*R^n := by field_simp
      rw [he]
      nlinarith [mul_nonneg hβ (pow_nonneg hR.le n)]
  apply hbase.trans
  have hmul:=mul_le_mul_of_nonneg_left hn (mul_nonneg hcoef.le (pow_nonneg hr0.le n))
  have he : q^n*r^n=R^n := by rw [←mul_pow,div_mul_cancel₀ R hr0.ne']
  calc
    _=(1+β/R)*r^n*(((n:ℝ)+1)*q^n) := by rw [←he]; ring
    _≤(1+β/R)*r^n*S := hmul
    _=_ := by ring

/-- A uniform exponential majorant bounds the actual limsup of horizon roots. -/
theorem limsup_root_le_of_exponential {u : ℕ→ℝ} (hu : ∀ n,0≤u n)
    {C r : ℝ} (hC : 0<C) (hr : 0≤r) (hbound : ∀ n,u n≤C*r^n) :
    limsup (fun n : ℕ=>u n^((n:ℝ)⁻¹)) atTop≤r := by
  have hinv : Tendsto (fun n : ℕ=>(n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ=>C^((n:ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero,Function.comp_def] using
      (Real.continuousAt_const_rpow (a:=C) (b:=0) hC.ne').tendsto.comp hinv
  have hg : Tendsto (fun n : ℕ=>C^((n:ℝ)⁻¹)*r) atTop (𝓝 r) := by
    simpa only [one_mul] using hc.mul_const r
  have hh : ∀ᶠ n : ℕ in atTop,u n^((n:ℝ)⁻¹)≤C^((n:ℝ)⁻¹)*r := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    calc
      _≤(C*r^n)^((n:ℝ)⁻¹) := Real.rpow_le_rpow (hu n) (hbound n) (by positivity)
      _=C^((n:ℝ)⁻¹)*r := by
        rw [Real.mul_rpow hC.le (pow_nonneg hr n),Real.pow_rpow_inv_natCast hr (by omega)]
  have hl:=limsup_le_limsup hh
    (isCoboundedUnder_le_of_le atTop (fun n=>Real.rpow_nonneg (hu n) _)) hg.isBoundedUnder_le
  rwa [hg.limsup_eq] at hl

/-- The uniform polynomial envelope has at most its stated exponential factor. -/
theorem limsup_root_le_of_quadraticEnvelope {u : ℕ→ℝ} (hu : ∀ n,0≤u n)
    {R β : ℝ} (hR : 0<R) (hβ : 0≤β)
    (hbound : ∀ n,u n≤quadraticEnvelope R β n) :
    limsup (fun n : ℕ=>u n^((n:ℝ)⁻¹)) atTop≤R := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨s,hRs,hsr⟩:=exists_between hr
  obtain ⟨C,hC,hCr⟩:=quadraticEnvelope_exponential hR hβ hRs
  exact (limsup_root_le_of_exponential hu hC (hR.trans hRs).le
    (fun n=>(hbound n).trans (hCr n))).trans_lt hsr

end polyak.General
