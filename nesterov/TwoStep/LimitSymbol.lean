import nesterov.TwoStep.LagPolynomial
import nesterov.TwoStep.AsymptoticsBridge
import nesterov.Quadratic.ScaledJury
import nesterov.Trace.Model
import nesterov.Faithful.Algebra

/-! Exact positivity region of the limiting lag-one symbol, including both
boundary inequalities and strict middle-quadratic stability. -/
namespace nesterov.TwoStep
noncomputable section
open Set Filter
open scoped Topology

def limitSymbol (τ y ξ : ℝ) : ℝ := ξ^2/y^2*(2*y*(2*τ-1)+4*(1-τ*y)*ξ)

theorem affine_nonnegative_iff (A B : ℝ) :
    (∀ ξ∈Ioc (0:ℝ) 2,0≤A+B*ξ) ↔ 0≤A ∧ 0≤A+2*B := by
  constructor
  · intro h
    constructor
    · have hid : Tendsto (fun ξ : ℝ=>ξ) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      have ht : Tendsto (fun ξ : ℝ=>A+B*ξ) (𝓝[>] (0:ℝ)) (𝓝 A) := by
        simpa only [mul_zero,add_zero] using tendsto_const_nhds.add
          (tendsto_const_nhds.mul hid)
      apply ge_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by norm_num : (0:ℝ)<2)).filter_mono nhdsWithin_le_nhds] with ξ hξ hξ2
      exact h ξ ⟨hξ,hξ2.le⟩
    · simpa only [mul_comm B 2] using h 2 ⟨by norm_num,le_rfl⟩
  · rintro ⟨hA,hB⟩ ξ hξ
    have he : A+B*ξ=(1-ξ/2)*A+(ξ/2)*(A+2*B) := by ring
    rw [he]
    exact add_nonneg (mul_nonneg (by linarith [hξ.2]) hA) (mul_nonneg (by linarith [hξ.1]) hB)

theorem affine_positive_iff (A B : ℝ) :
    (∀ ξ∈Ioc (0:ℝ) 2,0<A+B*ξ) ↔ 0≤A ∧ 0<A+2*B := by
  constructor
  · intro h
    exact ⟨((affine_nonnegative_iff A B).mp (fun ξ hξ=>(h ξ hξ).le)).1,
      by simpa only [mul_comm B 2] using h 2 ⟨by norm_num,le_rfl⟩⟩
  · rintro ⟨hA,hB⟩ ξ hξ
    have he : A+B*ξ=(1-ξ/2)*A+(ξ/2)*(A+2*B) := by ring
    rw [he]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [hξ.2]) hA)
      (mul_pos (by linarith [hξ.1]) hB)

theorem limitSymbol_nonnegative_iff {τ y : ℝ} (hy : 0<y) :
    (∀ ξ∈Ioc (0:ℝ) 2,0≤limitSymbol τ y ξ) ↔ 1/2≤τ ∧ y*(1+2*τ)≤4 := by
  have hp (ξ : ℝ) (hξ : ξ∈Ioc (0:ℝ) 2) : 0<ξ^2/y^2 := div_pos (sq_pos_of_pos hξ.1) (sq_pos_of_pos hy)
  have he : (∀ ξ∈Ioc (0:ℝ) 2,0≤limitSymbol τ y ξ) ↔
      ∀ ξ∈Ioc (0:ℝ) 2,0≤2*y*(2*τ-1)+4*(1-τ*y)*ξ := by
    apply forall_congr'
    intro ξ
    apply forall_congr'
    intro hξ
    exact mul_nonneg_iff_of_pos_left (hp ξ hξ)
  rw [he,affine_nonnegative_iff]
  constructor
  · rintro ⟨ha,hb⟩
    have ht : 0≤2*τ-1 := (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num) hy)).mp ha
    constructor <;> nlinarith
  · rintro ⟨ht,hyτ⟩
    constructor
    · exact mul_nonneg (by positivity) (by linarith)
    · nlinarith

theorem limitSymbol_positive_iff {τ y : ℝ} (hy : 0<y) :
    (∀ ξ∈Ioc (0:ℝ) 2,0<limitSymbol τ y ξ) ↔ 1/2≤τ ∧ y*(1+2*τ)<4 := by
  have hp (ξ : ℝ) (hξ : ξ∈Ioc (0:ℝ) 2) : 0<ξ^2/y^2 := div_pos (sq_pos_of_pos hξ.1) (sq_pos_of_pos hy)
  have he : (∀ ξ∈Ioc (0:ℝ) 2,0<limitSymbol τ y ξ) ↔
      ∀ ξ∈Ioc (0:ℝ) 2,0<2*y*(2*τ-1)+4*(1-τ*y)*ξ := by
    apply forall_congr'
    intro ξ
    apply forall_congr'
    intro hξ
    exact mul_pos_iff_of_pos_left (hp ξ hξ)
  rw [he,affine_positive_iff]
  constructor
  · rintro ⟨ha,hb⟩
    have ht : 0≤2*τ-1 := (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num) hy)).mp ha
    constructor <;> nlinarith
  · rintro ⟨ht,hyτ⟩
    constructor
    · exact mul_nonneg (by positivity) (by linarith)
    · nlinarith

/-- The two-step limiting stationary method, in exactly the source normalization. -/
def limitData (τ y : ℝ) (hy : 0<y) : Trace.DoubleRootData where
  method := Momentum.method 1 τ y hy.ne'
  q := Polynomial.C (-1/y)
  y := y
  y_pos := hy
  factor := by
    rw [method_recurrencePolynomial]
    have hc : (1+1)/y=(-1/y)*(-2) := by ring
    rw [hc,map_mul]
    simp only [map_neg,map_ofNat,map_one,mul_one,neg_div,one_div ]
    ring
  q_one := by simp

 theorem limitData_query (τ y : ℝ) (hy : 0<y) :
    (limitData τ y hy).u=Polynomial.C (1+τ)*Polynomial.X-Polynomial.C τ := by
  change (Momentum.method 1 τ y hy.ne').queryPolynomial=_
  rw [method_queryPolynomial]
  simp
  ring

 theorem limitData_lead (τ y : ℝ) (hy : 0<y) :
    (limitData τ y hy).effectiveLead=τ := by
  change Faithful.effectiveLead (limitData τ y hy).u (Polynomial.C (-1/y)) y=τ
  rw [limitData_query]
  exact Faithful.effectiveLead_momentum τ y

 theorem limitData_symbol (τ y ω : ℝ) (hy : 0<y) :
    (limitData τ y hy).symbol ω=limitSymbol τ y (1-Real.cos ω) := by
  unfold Trace.DoubleRootData.symbol
  dsimp only
  rw [Trace.DoubleRootData.eval_phi,Trace.DoubleRootData.eval_phi]
  have hc (lam : ℝ) (z : ℂ) : -(Momentum.method 1 τ y hy.ne').characteristic lam z=
      ((1/y:ℝ):ℂ)*Quadratic.characteristic 1 τ y lam z := by
    rw [Momentum.method_characteristic]
    push_cast
    ring
  change ((1-Complex.exp ((ω:ℂ)*Complex.I))*(-(Momentum.method 1 τ y hy.ne').characteristic 0 _)*
    star (-(Momentum.method 1 τ y hy.ne').characteristic 1 _)).re=_
  rw [hc,hc]
  have he : Complex.exp ((ω:ℂ)*Complex.I)=circle 1 ω := by simp [circle,polyak.Waves.z]
  rw [he]
  have hr : star ((1/y:ℝ):ℂ)=((1/y:ℝ):ℂ) := by simp
  have hh : ((1-circle 1 ω)*(((1/y:ℝ):ℂ)*Quadratic.characteristic 1 τ y 0 (circle 1 ω))*
      star (((1/y:ℝ):ℂ)*Quadratic.characteristic 1 τ y 1 (circle 1 ω))).re=
      (1/y)^2*((1-circle 1 ω)*Quadratic.characteristic 1 τ y 0 (circle 1 ω)*
        star (Quadratic.characteristic 1 τ y 1 (circle 1 ω))).re := by
    rw [star_mul,hr]
    have heq : (1-circle 1 ω)*(((1/y:ℝ):ℂ)*Quadratic.characteristic 1 τ y 0 (circle 1 ω))*
        (star (Quadratic.characteristic 1 τ y 1 (circle 1 ω))*((1/y:ℝ):ℂ))=
        (((1/y)^2:ℝ):ℂ)*((1-circle 1 ω)*Quadratic.characteristic 1 τ y 0 (circle 1 ω)*
          star (Quadratic.characteristic 1 τ y 1 (circle 1 ω))) := by
      rw [Complex.ofReal_pow]
      ring
    rw [heq]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hh,physical_lagOne_polynomial]
  simp only [mul_zero,mul_one,Ltau_limit]
  unfold limitSymbol
  ring

 theorem half_circle_parameters (P : ℝ→Prop) :
    (∀ ω∈Ioc (0:ℝ) Real.pi,P (1-Real.cos ω)) ↔ ∀ ξ∈Ioc (0:ℝ) 2,P ξ := by
  constructor
  · intro h ξ hξ
    have hb : -1≤1-ξ ∧ 1-ξ≤1 := ⟨by linarith [hξ.2],by linarith [hξ.1]⟩
    have he : 1-Real.cos (Real.arccos (1-ξ))=ξ := by rw [Real.cos_arccos hb.1 hb.2];ring
    have hp : 0<Real.arccos (1-ξ) := Real.arccos_pos.mpr (by linarith [hξ.1])
    rw [←he]
    exact h _ ⟨hp,Real.arccos_le_pi _⟩
  · intro h ω hω
    have hx : 0<1-Real.cos ω := by
      have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hω.2 hω.1
      simpa only [Real.cos_zero] using sub_pos.mpr hh
    exact h _ ⟨hx,by linarith [Real.neg_one_le_cos ω]⟩

 theorem limit_method_positive_iff (τ y : ℝ) (hy : 0<y) :
    (∀ ω∈Ioc (0:ℝ) Real.pi,0<(limitData τ y hy).symbol ω) ↔
      1/2≤τ ∧ y*(1+2*τ)<4 := by
  simp only [limitData_symbol]
  rw [half_circle_parameters (fun ξ=>0<limitSymbol τ y ξ),limitSymbol_positive_iff hy]

 theorem limit_method_nonnegative_iff (τ y : ℝ) (hy : 0<y) :
    (∀ ω∈Ioc (0:ℝ) Real.pi,0≤(limitData τ y hy).symbol ω) ↔
      1/2≤τ ∧ y*(1+2*τ)≤4 := by
  simp only [limitData_symbol]
  rw [half_circle_parameters (fun ξ=>0≤limitSymbol τ y ξ),limitSymbol_nonnegative_iff hy]

 theorem limit_middle_roots_lt {τ y : ℝ} (hy : 0<y) (hτ : 1/2≤τ)
    (hbound : y*(1+2*τ)<4) {z : ℂ}
    (hz : Trace.eval ((limitData τ y hy).u-Polynomial.C 2*(limitData τ y hy).v) z=0) : ‖z‖<1 := by
  have hv : (limitData τ y hy).v=(Polynomial.X-Polynomial.C 1)^2*Polynomial.C (-1/y) :=
    (limitData τ y hy).factor
  have he : Trace.eval ((limitData τ y hy).u-Polynomial.C 2*(limitData τ y hy).v) z=
      ((2/y:ℝ):ℂ)*Quadratic.characteristic 1 τ y (1/2) z := by
    rw [Trace.eval_sub,Trace.eval_mul,Trace.eval_C,limitData_query,
      hv]
    simp only [Trace.eval_sub,Trace.eval_mul,Trace.eval_pow,Trace.eval_X,Trace.eval_C]
    unfold Quadratic.characteristic Quadratic.queryPolynomial
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
    ring
  rw [he] at hz
  have hc : Quadratic.characteristic 1 τ y (1/2) z=0 :=
    (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr (div_ne_zero (by norm_num) hy.ne'))
  apply Quadratic.root_norm_lt_one (a:=Quadratic.S 1 τ y (1/2)) (q:=Quadratic.Q 1 τ y (1/2))
  · unfold Quadratic.Q
    nlinarith [mul_pos hy (show 0<τ by linarith)]
  · rw [abs_lt]
    unfold Quadratic.S Quadratic.Q
    constructor <;> nlinarith
  · exact (Quadratic.characteristic_eq _ _ _ _ _).symm.trans hc

 theorem half_wall_symbol (y ξ : ℝ) : limitSymbol (1/2) y ξ=2*(2-y)/y^2*ξ^3 := by
  unfold limitSymbol
  ring

end
end nesterov.TwoStep
