import nesterov.TwoStep.LagPolynomial
import nesterov.Phase.Defect
import nesterov.Phase.AngleEndpoint
import nesterov.Phase.Cycles
import nesterov.Phase.Mixed

/-! The exact sign of the lag-one quadratic is the source's principal phase test. -/
namespace nesterov.TwoStep
noncomputable section
open Set Spectral Phase

theorem stable_lagOne_positive_factor (q : Momentum.Tuning) {μ L ω : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (hω : ω∈Ioc (0:ℝ) Real.pi) :
    ∃ A : ℝ,0<A ∧
      (1-Real.cos ω)*Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) (1-Real.cos ω)=
        A*Real.sin (momentumAngle q μ L ω-ω/2) := by
  let M := Momentum.method q.beta q.tau q.stepSize q.step_pos.ne'
  let a := M.symbolPair μ L 0
  have hne : g a (frequency ω)≠0 ∨ skew a (frequency ω)≠0 := by
    rcases hω.2.lt_or_eq with hw | rfl
    · exact Or.inr (momentum_skew_pos q hμL ⟨hω.1,hw⟩).ne'
    · exact Or.inl (momentum_endpoint_pair q hμ hμL hs).1.ne
  obtain ⟨A,hA,he⟩ := stationary_lag_one_positive_factor M hμL hω hne
  have hez : Complex.exp ((ω:ℂ)*Complex.I)=circle 1 ω := by simp [circle,polyak.Waves.z]
  rw [hez,Momentum.method_characteristic,Momentum.method_characteristic] at he
  have hprod : ((1-circle 1 ω)*(-(1/(q.stepSize:ℂ))*
      Quadratic.characteristic q.beta q.tau q.stepSize μ (circle 1 ω))*
      star (-(1/(q.stepSize:ℂ))*Quadratic.characteristic q.beta q.tau q.stepSize L (circle 1 ω))).re=
      (1/q.stepSize^2)*((1-circle 1 ω)*Quadratic.characteristic q.beta q.tau q.stepSize μ (circle 1 ω)*
        star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle 1 ω))).re := by
    have hr (x : ℝ) : star (x:ℂ)=(x:ℂ) := by simp
    calc
      _=(((1/q.stepSize^2:ℝ):ℂ)*((1-circle 1 ω)*
        Quadratic.characteristic q.beta q.tau q.stepSize μ (circle 1 ω)*
        star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle 1 ω)))).re := by
        congr 1
        simp only [star_mul,star_neg,one_div,star_inv₀,hr]
        push_cast
        ring
      _=_ := by simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hprod,physical_lagOne_polynomial] at he
  refine ⟨q.stepSize^2*A,mul_pos (sq_pos_of_pos q.step_pos) hA,?_⟩
  change _=q.stepSize^2*A*Real.sin (angle (g a (frequency ω)) (skew a (frequency ω))-ω/2)
  calc
    _=q.stepSize^2*((1/q.stepSize^2)*((1-Real.cos ω)*
      Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) (1-Real.cos ω))) := by
        field_simp [q.step_pos.ne']
    _=q.stepSize^2*(A*Real.sin (angle (g a (frequency ω)) (skew a (frequency ω))-ω/2)) :=
      congrArg (fun v : ℝ=>q.stepSize^2*v) he
    _=_ := by ring

theorem stable_Ltau_phase_sign (q : Momentum.Tuning) {μ L ω : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (hω : ω∈Ioc (0:ℝ) Real.pi) :
    (0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) (1-Real.cos ω) ↔
      ω/2<momentumAngle q μ L ω) ∧
    (Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) (1-Real.cos ω)=0 ↔
      momentumAngle q μ L ω=ω/2) ∧
    (Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) (1-Real.cos ω)<0 ↔
      momentumAngle q μ L ω<ω/2) := by
  obtain ⟨A,hA,he⟩ := stable_lagOne_positive_factor q hμ hμL hs hω
  have hξ : 0<1-Real.cos ω := sub_pos.mpr (by simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hω.2 hω.1)
  have hθ := momentumAngle_mem_Ioc q hμ hμL hs hω
  have hlo : -Real.pi<momentumAngle q μ L ω-ω/2 := by linarith [Real.pi_pos,hθ.1,hω.2]
  have hhi : momentumAngle q μ L ω-ω/2<Real.pi := by linarith [hθ.2,hω.1]
  have hp : 0<Real.sin (momentumAngle q μ L ω-ω/2) ↔ 0<momentumAngle q μ L ω-ω/2 := by
    constructor
    · intro h
      by_contra hn
      have hx : momentumAngle q μ L ω-ω/2≤0 := le_of_not_gt hn
      have hh := Real.sin_nonpos_of_nonpos_of_neg_pi_le hx hlo.le
      linarith
    · intro h
      exact Real.sin_pos_of_pos_of_lt_pi h hhi
  have hz := Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi
  have hn : Real.sin (momentumAngle q μ L ω-ω/2)<0 ↔ momentumAngle q μ L ω-ω/2<0 := by
    constructor
    · intro h
      by_contra hn
      have hh := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_not_gt hn) hhi.le
      linarith
    · intro h
      exact Real.sin_neg_of_neg_of_neg_pi_lt h hlo
  constructor
  · constructor
    · intro h
      have hh : 0<Real.sin (momentumAngle q μ L ω-ω/2) :=
        (mul_pos_iff_of_pos_left hA).mp (he ▸ mul_pos hξ h)
      linarith [(hp.mp hh)]
    · intro h
      have hh := mul_pos hA (hp.mpr (sub_pos.mpr h))
      rw [←he] at hh
      exact (mul_pos_iff_of_pos_left hξ).mp hh
  constructor
  · constructor
    · intro h
      have hh : Real.sin (momentumAngle q μ L ω-ω/2)=0 := by rw [h,mul_zero] at he;exact (mul_eq_zero.mp he.symm).resolve_left hA.ne'
      linarith [hz.mp hh]
    · intro h
      rw [h,sub_self,Real.sin_zero,mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hξ.ne'
  · constructor
    · intro h
      have hh : Real.sin (momentumAngle q μ L ω-ω/2)<0 :=
        by
          have hh := he ▸ mul_neg_of_pos_of_neg hξ h
          nlinarith only [hh,hA]
      linarith [hn.mp hh]
    · intro h
      have hh := mul_neg_of_pos_of_neg hA (hn.mpr (sub_neg.mpr h))
      rw [←he] at hh
      nlinarith only [hh,hξ]

/-- The negative-polynomial test at a rational angle gives strict growth from rest. -/
theorem negative_Ltau_restRate (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) {K : ℕ} (hK : 3≤K)
    (hneg : Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L)
      (1-Real.cos (2*Real.pi/K))<0) :
    1<Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  have hangle : 2*Real.pi/K∈Ioo (0:ℝ) Real.pi := by
    simpa [polyak.General.Regions.rationalAngle] using polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
  have hp := ((stable_Ltau_phase_sign q hμ hμL hs ⟨hangle.1,hangle.2.le⟩).2.2.mp hneg)
  apply one_lt_restRate_of_strict_phase q hμ hμL hs hK (j:=1) le_rfl (by omega) (by simp)
  rw [show 2*Real.pi/(K:ℝ)/2=Real.pi/K by ring] at hp
  simpa only [Nat.cast_one,mul_one] using hp

/-- Positivity on the source interval gives a strict full-class rate bound. -/
theorem positive_Ltau_rate (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (hpos : ∀ ξ∈Ioc (0:ℝ) 2,0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) ξ) :
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<1 := by
  apply momentumRate_lt_one_of_lagOne q hμ hμL hs
  intro z hz hz1
  have he : circle 1 z.arg=z := by
    simpa [circle,polyak.Waves.z,hz] using Complex.norm_mul_exp_arg_mul_I z
  rw [←he,physical_lagOne_polynomial]
  have hξ : 0<1-Real.cos z.arg := by
    have hn : Real.cos z.arg≠1 := by
      intro hn
      have hc : z.re=1 := by
        have hh := congrArg Complex.re he
        have hcoord : (circle 1 z.arg).re=Real.cos z.arg := by simpa using circle_pow_re 1 z.arg 1
        rw [hcoord,hn] at hh
        exact hh.symm
      have hi : z.im=0 := by
        have hs : z.re^2+z.im^2=1 := by
          have hh := Complex.normSq_eq_norm_sq z
          rw [hz] at hh
          simpa [Complex.normSq_apply,pow_two] using hh
        rw [hc] at hs
        nlinarith [sq_nonneg z.im]
      exact hz1 (Complex.ext (by simpa using hc) (by simpa using hi))
    exact sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one _) hn)
  exact mul_pos hξ (hpos _ ⟨hξ,by linarith [Real.neg_one_le_cos z.arg]⟩)

end
end nesterov.TwoStep
