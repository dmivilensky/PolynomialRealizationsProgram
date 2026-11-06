import nesterov.Phase.LagOne
import nesterov.Momentum.QuadraticDictionary

/-!
Article: Proposition `prop:lagone` (b,c), including the balanced endpoint repair.
Use: exact lag-one/upper-lag-two weights and the actual unit-circle endpoint symbols.
-/
namespace nesterov.Phase
noncomputable section
open Spectral Duality Set

def mixed (a : SymbolPair) (lam : ℝ) (c : Frequency) : ℝ :=
  lagOne a 0 c+lam*(lagA a 0 2 c+lagB a 2 c)

def endpoint : Frequency := ⟨1,by norm_num,le_rfl⟩

@[simp] theorem mixed_endpoint (a : SymbolPair) (lam : ℝ) : mixed a lam endpoint=0 := by
  simp [mixed,lagOne,endpoint,lagA,lagB,polyak.Waves.z]

theorem continuous_mixed (a : SymbolPair) (lam : ℝ) : Continuous (mixed a lam) :=
  (continuous_lagOne a 0).add (continuous_const.mul
    ((continuous_lagA a 0 2).add (continuous_lagB a 2)))

theorem mixed_symbol (a : SymbolPair) (lam η : ℝ) (c : Frequency) :
    symbol a 0 {1,2} (fun n=>if n=1 then 1 else 0) (fun n=>if n=2 then lam else 0)
      η η c=mixed a lam c+2*η*g a c := by
  have hL := lagOne_symbol a 0 c
  simp only [Real.exp_zero,Real.sinh_zero,neg_mul] at hL
  simp only [symbol,Finset.sum_insert,Finset.mem_singleton,show (1:ℕ)≠2 by norm_num,
    not_false_eq_true,Finset.sum_singleton,ite_eq_left,ite_eq_right,
    one_mul,zero_mul,add_zero] at hL ⊢
  dsimp [mixed]
  rw [←hL]
  ring

/-- The minimizer multiplier removes the sole unit-circle contact at z=1. -/
theorem mixed_certificate {a : SymbolPair} {lam : ℝ} (hlam : 0≤lam)
    (hg : g a endpoint<0) (hneg : ∀ c,c≠endpoint → mixed a lam c<0) :
    Nonempty (Duality.StrictCertificate a 0) := by
  have hnonpos (c : Frequency) : mixed a lam c≤0 := by
    by_cases hc : c=endpoint
    · simp [hc]
    · exact (hneg c hc).le
  have hstrict (c : Frequency) (hc : 0≤g a c) : mixed a lam c<0 := by
    apply hneg c
    intro he
    subst c
    linarith
  obtain ⟨η,hη,hstrict⟩ := polyak.General.Multipliers.balanced_perturbation
    (mixed a lam) (g a) (continuous_mixed a lam) (continuous_g a) hnonpos hstrict
  apply certificate_of_negative a 0 {1,2} (fun n=>if n=1 then 1 else 0)
    (fun n=>if n=2 then lam else 0) η η
  · intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl <;> norm_num
  · intro n _
    split <;> norm_num
  · intro n _
    split <;> positivity
  · exact hη.le
  · exact hη.le
  · simp
  · intro c
    rw [mixed_symbol]
    exact hstrict c

/-- At z=1 the actual normalized gradient amplitude exceeds the query amplitude. -/
theorem stationary_g_endpoint (M : StationaryMethod) {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    g (M.symbolPair μ L 0) endpoint<0 := by
  have hz : polyak.Waves.z 0 (Real.arccos (endpoint:Frequency))=1 := by
    simp [endpoint,polyak.Waves.z]
  unfold g
  rw [M.symbolPair_u,M.symbolPair_p,hz]
  have hu : (M.queryPolynomial.map Complex.ofRealHom).eval (1:ℂ)=1 := by
    rw [M.queryPolynomial_complex_eval]
    simp only [one_pow,mul_one]
    exact_mod_cast M.query_sum
  have hv : (M.recurrencePolynomial.map Complex.ofRealHom).eval (1:ℂ)=0 := by
    rw [M.recurrencePolynomial_complex_eval]
    simp only [one_pow,mul_one]
    exact_mod_cast M.recurrence_sum
  rw [M.normalizedPolynomial_complex_eval,hu,hv]
  simp only [mul_one,mul_zero,sub_zero,Complex.normSq_one,Complex.normSq_ofReal]
  have hratio : 1<(L+μ)/(L-μ) := (lt_div_iff₀ (sub_pos.mpr hμL)).mpr (by linarith)
  nlinarith

/-- A stable tuning lies above the exact middle-quadratic threshold at t=0. -/
theorem middleRadius_lt_one_of_stable (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) :
    IQC.middleRadius (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L<1 := by
  have hh := IQC.middleRadius_le_quadraticRate (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') hμ hμL
  rw [Momentum.quadraticRate_method] at hh
  exact hh.trans_lt ((Quadratic.stable_iff_quadraticRate_lt_one hμL.le).mp hs)

/-- The exact complex multiplier of the upper lag-two constraint. -/
theorem upper_two_complex (a : SymbolPair) (c : Frequency) :
    lagA a 0 2 c+lagB a 2 c=
      ((((g a c:ℝ):ℂ)-2*Complex.I*skew a c)*
        (1-star (polyak.Waves.z 0 (Real.arccos c))^2)).re := by
  have hre : (star (polyak.Waves.z 0 (Real.arccos c))^2).re=Real.cos (2*Real.arccos c) := by
    rw [←star_pow]
    change (polyak.Waves.z 0 (Real.arccos c)^2).re=Real.cos (2*Real.arccos c)
    simpa using polyak.Waves.z_pow_re 0 (Real.arccos c) 2
  have him : (star (polyak.Waves.z 0 (Real.arccos c))^2).im= -Real.sin (2*Real.arccos c) := by
    rw [←star_pow]
    change -(polyak.Waves.z 0 (Real.arccos c)^2).im= -Real.sin (2*Real.arccos c)
    exact congrArg Neg.neg (by simpa using polyak.Waves.z_pow_im 0 (Real.arccos c) 2)
  simp only [lagA,lagB,mul_zero,Real.cosh_zero,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,
    Complex.one_im,Complex.I_re,Complex.I_im,hre,him]
  norm_num

theorem mixed_complex (a : SymbolPair) (lam : ℝ) (c : Frequency) :
    mixed a lam c=
      ((((g a c:ℝ):ℂ)-2*Complex.I*skew a c)*
        ((1-polyak.Waves.z 0 (Real.arccos c))+
          (lam:ℂ)*(1-star (polyak.Waves.z 0 (Real.arccos c))^2))).re := by
  rw [mixed,upper_two_complex]
  unfold lagOne
  simp only [mul_add,Complex.add_re,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem mixed_momentum (q : Momentum.Tuning) {μ L : ℝ} (hμL : μ<L)
    (lam : ℝ) (c : Frequency) :
    mixed ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0) lam c=
      -(4/(q.stepSize^2*(L-μ)^2))*
        (Quadratic.characteristic q.beta q.tau q.stepSize μ (polyak.Waves.z 0 (Real.arccos c))*
          star (Quadratic.characteristic q.beta q.tau q.stepSize L (polyak.Waves.z 0 (Real.arccos c)))*
          ((1-polyak.Waves.z 0 (Real.arccos c))+
            (lam:ℂ)*(1-star (polyak.Waves.z 0 (Real.arccos c))^2))).re := by
  rw [mixed_complex,momentum_factor hμL q.step_pos.ne']
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im]
  ring

/-- Proposition lagone(c), retaining the upper lag-two direction and λ≥0. -/
theorem momentumRate_lt_one_of_mixed (q : Momentum.Tuning) {μ L lam : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (hlam : 0≤lam)
    (hpos : ∀ z : ℂ,‖z‖=1 → z≠1 →
      0<(Quadratic.characteristic q.beta q.tau q.stepSize μ z*
        star (Quadratic.characteristic q.beta q.tau q.stepSize L z)*
        ((1-z)+(lam:ℂ)*(1-star z^2))).re) :
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<1 := by
  obtain ⟨cert⟩ := mixed_certificate hlam (stationary_g_endpoint _ hμ hμL) (fun c hc=>by
    rw [mixed_momentum q hμL]
    have hz : ‖polyak.Waves.z 0 (Real.arccos c)‖=1 := by
      simpa using polyak.Waves.norm_z_pow 0 (Real.arccos c) 1
    have hz1 : polyak.Waves.z 0 (Real.arccos c)≠1 := by
      intro h
      have hr := congrArg Complex.re h
      have hre := polyak.Waves.z_pow_re 0 (Real.arccos c) 1
      simp only [pow_one,Nat.cast_one,one_mul,mul_zero,Real.exp_zero,Complex.one_re] at hre hr
      rw [hr,Real.cos_arccos c.2.1 c.2.2] at hre
      apply hc
      exact Subtype.ext hre.symm
    have hp := hpos _ hz hz1
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos
      (div_pos (by norm_num) (mul_pos (pow_pos q.step_pos _) (pow_pos (sub_pos.mpr hμL) _)))) hp)
  simpa only [Momentum.momentumRate,Real.exp_zero] using IQC.one_exponent hμ hμL
    (by simpa using middleRadius_lt_one_of_stable q hμ hμL hs) cert

/-- Proposition lagone(b) is the literal λ=0 specialization. -/
theorem momentumRate_lt_one_of_lagOne (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (hpos : ∀ z : ℂ,‖z‖=1 → z≠1 →
      0<((1-z)*Quadratic.characteristic q.beta q.tau q.stepSize μ z*
        star (Quadratic.characteristic q.beta q.tau q.stepSize L z)).re) :
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<1 := by
  apply momentumRate_lt_one_of_mixed q hμ hμL hs (lam:=0) le_rfl
  intro z hz hz1
  simpa only [Complex.ofReal_zero,zero_mul,add_zero,mul_assoc,mul_comm,mul_left_comm] using hpos z hz hz1

end
end nesterov.Phase
