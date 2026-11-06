import nesterov.Trace.CurvatureBounds
import Mathlib.Topology.Order.Monotone

/-! The closed-root trace bound and endpoint rigidity. All limiting arguments
are at fixed exterior real points, so possible unit-circle poles cause no loss. -/
namespace nesterov.Trace
noncomputable section
open Polynomial Complex Metric Set Real Filter
open scoped Topology
namespace DoubleRootData
variable (A : DoubleRootData)

def ClosedPencil (lam0 : ℝ) : Prop :=
  ∀ lam∈Ioo lam0 1,∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖≤1

theorem exterior_fraction_bounds {lam0 lam : ℝ} (h0 : 0≤lam0)
    (hclosed : A.ClosedPencil lam0) (hcop : IsCoprime A.u A.v)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) (hlam : lam∈Ioo lam0 1)
    {z : ℝ} (hz : 1<z) :
    0≤(Polynomial.eval z A.numerator/Polynomial.eval z (A.phi lam)-1) ∧
      Polynomial.eval z A.numerator/Polynomial.eval z (A.phi lam)-1≤2/(lam*A.y)-1 := by
  have hl0 : 0<lam := h0.trans_lt hlam.1
  have hs := A.curvature_strict_of_closed hcop hS hl0 hlam.2 (hclosed lam hlam)
  let Q := A.curvatureQuotient lam hs
  have hz0 : z≠0 := (lt_trans zero_lt_one hz).ne'
  have hx0 : 0<1/z := one_div_pos.mpr (lt_trans zero_lt_one hz)
  have hx1 : 1/z<1 := (div_lt_one (lt_trans zero_lt_one hz)).mpr hz
  have hd : eval (A.phi lam) (z:ℂ)≠0 := by
    intro he
    have hh := hs (z:ℂ) he
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one hz)] at hh
    exact not_lt_of_ge hz.le hh
  have hi : (((1/z:ℝ):ℂ))⁻¹=(z:ℂ) := by
    simp only [one_div,Complex.ofReal_inv,inv_inv]
  have hf := Q.diskFunction_reciprocal (Complex.ofReal_ne_zero.mpr (one_div_ne_zero hz0))
    (by change eval (A.phi lam) (((1/z:ℝ):ℂ))⁻¹≠0;rw [hi];exact hd)
  change Q.diskFunction (((1/z:ℝ):ℂ))=eval A.numerator (((1/z:ℝ):ℂ))⁻¹/
    eval (A.phi lam) (((1/z:ℝ):ℂ))⁻¹-1 at hf
  rw [hi,eval_ofReal,eval_ofReal,←Complex.ofReal_div,←Complex.ofReal_one,←Complex.ofReal_sub] at hf
  have hb := A.curvature_radial_bounds hl0 hlam.2 hs hS hx0 hx1
  rw [hf,Complex.ofReal_re] at hb
  exact hb

theorem endpoint_step_bound_coprime {lam0 : ℝ} (h0 : 0≤lam0) (h1 : lam0<1)
    (hclosed : A.ClosedPencil lam0) (hcop : IsCoprime A.u A.v)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) : A.y≤2 := by
  have hstep (lam : ℝ) (hlam : lam∈Ioo lam0 1) : lam*A.y≤2 := by
    have hb := A.exterior_fraction_bounds h0 hclosed hcop hS hlam (z:=2) (by norm_num)
    have hp : 0<lam*A.y := mul_pos (h0.trans_lt hlam.1) A.y_pos
    have hh : 1≤2/(lam*A.y) := by linarith
    simpa only [one_mul] using (le_div_iff₀ hp).mp hh
  by_contra hh
  have hy : 2<A.y := lt_of_not_ge hh
  have hmax : max lam0 (2/A.y)<1 := max_lt h1 ((div_lt_one A.y_pos).mpr hy)
  let lam := (max lam0 (2/A.y)+1)/2
  have hl : lam∈Ioo lam0 1 := by
    have he := le_max_left lam0 (2/A.y)
    constructor <;> dsimp [lam] <;> linarith
  have hgt : 2<lam*A.y := by
    apply (div_lt_iff₀ A.y_pos).mp
    have he := le_max_right lam0 (2/A.y)
    dsimp [lam]
    linarith
  exact not_lt_of_ge (hstep lam hl) hgt

theorem endpoint_rigidity_coprime {lam0 : ℝ} (h0 : 0≤lam0) (h1 : lam0<1)
    (hclosed : A.ClosedPencil lam0) (hcop : IsCoprime A.u A.v)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) (hy : A.y=2) : A.tmmTransfer := by
  have heq (z : ℝ) (hz : 1<z) (hd : Polynomial.eval z (A.phi 1)≠0) :
      Polynomial.eval z A.numerator=Polynomial.eval z (A.phi 1) := by
    have hc : Continuous (fun lam : ℝ=>Polynomial.eval z (A.phi lam)) := by
      unfold phi
      simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
      fun_prop
    have hr : Tendsto (fun lam : ℝ=>Polynomial.eval z A.numerator/Polynomial.eval z (A.phi lam)-1)
        (𝓝[<] (1:ℝ)) (𝓝 (Polynomial.eval z A.numerator/Polynomial.eval z (A.phi 1)-1)) :=
      ((continuousAt_const.div hc.continuousAt hd).sub continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
    have hu : Tendsto (fun lam : ℝ=>2/(lam*A.y)-1) (𝓝[<] (1:ℝ)) (𝓝 0) := by
      have hc2 : ContinuousAt (fun lam : ℝ=>2/(lam*A.y)-1) (1:ℝ) :=
        (continuousAt_const.div (continuousAt_id.mul_const A.y)
          (by simpa using A.y_pos.ne')).sub_const 1
      have hh := hc2.tendsto.mono_left (nhdsWithin_le_nhds (s:=Iio (1:ℝ)))
      simpa only [one_mul,hy,div_self (by norm_num : (2:ℝ)≠0),sub_self] using hh
    have hb : ∀ᶠ lam in 𝓝[<] (1:ℝ),
        0≤Polynomial.eval z A.numerator/Polynomial.eval z (A.phi lam)-1 ∧
          Polynomial.eval z A.numerator/Polynomial.eval z (A.phi lam)-1≤2/(lam*A.y)-1 := by
      filter_upwards [Ioo_mem_nhdsLT h1] with lam hlam
      exact A.exterior_fraction_bounds h0 hclosed hcop hS hlam hz
    have hlo := ge_of_tendsto hr (hb.mono fun _ h=>h.1)
    have hhi := le_of_tendsto_of_tendsto hr hu (hb.mono fun _ h=>h.2)
    exact (div_eq_one_iff_eq hd).mp (sub_eq_zero.mp (le_antisymm hhi hlo))
  have hp0 : A.phi 1≠0 := by
    intro hh
    have he := A.phi_one 1
    rw [hh,Polynomial.eval_zero] at he
    norm_num at he
  have hfin : {z : ℝ|Polynomial.eval z (A.phi 1)=0}.Finite := Polynomial.finite_setOfPred_isRoot hp0
  have hinf : (Ioi (1:ℝ)\{z : ℝ|Polynomial.eval z (A.phi 1)=0}).Infinite :=
    (Set.Ioi_infinite (1:ℝ)).sdiff hfin
  have hpoly : A.numerator=A.phi 1 := Polynomial.eq_of_infinite_eval_eq _ _
    (hinf.mono fun z hz=>heq z hz.1 hz.2)
  exact A.numerator_eq_phi_iff_tmmTransfer.mp hpoly

/-- Theorem trace(b), with its original closed-root interval hypothesis.
Common independent modes are canceled by an actual stationary-method bridge. -/
theorem trace_bound_rigid {lam0 : ℝ} (h0 : 0≤lam0) (h1 : lam0<1)
    (hclosed : A.ClosedPencil lam0)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) :
    A.y≤2 ∧ (A.y=2 ↔ A.tmmTransfer) := by
  obtain ⟨R⟩ := A.exists_commonReduction
  have hBclosed : R.reduced.ClosedPencil lam0 := by
    intro lam hlam z hz
    apply hclosed lam hlam z
    rw [R.phi_factor,eval_mul,hz,mul_zero]
  have hBsymbol := R.symbol_nonneg hS
  have hstep := R.reduced.endpoint_step_bound_coprime h0 h1 hBclosed R.coprime hBsymbol
  rw [R.step_eq] at hstep
  refine ⟨hstep,?_,A.tmmTransfer_step⟩
  intro hy
  have hBy : R.reduced.y=2 := R.step_eq.trans hy
  have hB := R.reduced.endpoint_rigidity_coprime h0 h1 hBclosed R.coprime hBsymbol hBy
  unfold tmmTransfer at hB ⊢
  rw [R.u_factor,R.q_factor,hB]
  ring

end DoubleRootData
end
end nesterov.Trace
