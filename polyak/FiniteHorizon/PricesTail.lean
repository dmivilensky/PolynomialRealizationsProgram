import polyak.FiniteHorizon.PricesSize
import polyak.Growth.HorizonEnvelope

/-!
Article: Appendix C, the vanishing terminal term in Lemma prices.
Use: the actual finite-memory growth envelope controls every sampled position;
all continuous linear window prices therefore vanish after any stronger discount.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

theorem discounted_norm_sq_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) {C S t : ℝ} (hC : 0≤C) (hSt : S<t)
    (hx : ∀ n,‖x n‖≤C*Real.exp ((n : ℝ)*S)) (c : ℕ) :
    Tendsto (fun n : ℕ => Real.exp (-2*(n : ℝ)*t)*‖x (n+c)‖^2) atTop (𝓝 0) := by
  have hr : Real.exp (2*(S-t))<1:=Real.exp_lt_one_iff.mpr (by linarith)
  have hpow:=tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (2*(S-t))).le hr
  have hb (n : ℕ) : Real.exp (-2*(n : ℝ)*t)*‖x (n+c)‖^2≤
      (C^2*Real.exp (2*(c : ℝ)*S))*Real.exp (2*(S-t))^n := by
    have hs : Real.exp (((n+c : ℕ) : ℝ)*S)^2=Real.exp (2*(((n+c : ℕ) : ℝ)*S)) := by
      rw [←Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
    have hp : Real.exp (2*(S-t))^n=Real.exp ((n : ℝ)*(2*(S-t))):=(Real.exp_nat_mul _ _).symm
    have he : Real.exp (-2*(n : ℝ)*t)*Real.exp (((n+c : ℕ) : ℝ)*S)^2=
        Real.exp (2*(c : ℝ)*S)*Real.exp (2*(S-t))^n := by
      rw [hs,hp,←Real.exp_add,←Real.exp_add]
      congr 1
      push_cast
      ring
    calc
      _≤Real.exp (-2*(n : ℝ)*t)*(C*Real.exp (((n+c : ℕ) : ℝ)*S))^2 :=
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hx (n+c)))
          (Real.exp_pos _).le
      _=C^2*(Real.exp (-2*(n : ℝ)*t)*Real.exp (((n+c : ℕ) : ℝ)*S)^2) :=by ring
      _=_ :=by rw [he]; ring
  exact squeeze_zero (fun n => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hb
    (by simpa only [mul_zero] using tendsto_const_nhds.mul hpow)

def runWindow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H : ℕ} (r : HRun E A B β H) (k : ℕ) : WindowSpace H :=
  segmentWindow (r.segment k) k

theorem hRun_exists_norm_exp_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β S : ℝ} {H : ℕ} (hB : B≠0) (r : HRun E A B β H)
    (hR : growthRate A B β H<Real.exp S) :
    ∃ C : ℝ,0≤C ∧ ∀ n,‖r.x n‖≤C*Real.exp ((n : ℝ)*S) := by
  obtain ⟨C,hC,hEnv⟩:=Growth.FiniteHorizon.exists_envelope_le_mul_pow
    (A:=A) (β:=β) (H:=H) (R:=Real.exp S) hB hR
  refine ⟨C*stateNorm r.x 0,mul_nonneg hC.le (stateNorm_nonneg _ _),?_⟩
  intro n
  have he:=stateNorm_le_envelope_hilbert (r.segment n)
  change stateNorm r.x n≤envelope A B β H n*stateNorm r.x 0 at he
  have hb:=mul_le_mul_of_nonneg_right (hEnv n) (stateNorm_nonneg r.x 0)
  have hh:=(norm_left_le_stateNorm r.x n).trans (he.trans hb)
  rw [←Real.exp_nat_mul] at hh
  convert hh using 1
  ring

theorem discounted_run_trace_tendsto_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β C S t : ℝ} {H : ℕ} (r : HRun E A B β H) (hC : 0≤C) (hS : S<t)
    (hx : ∀ n,‖r.x n‖≤C*Real.exp ((n : ℝ)*S)) (k : ℕ) (hk : H≤k) :
    Tendsto (fun n : ℕ => Real.exp (-2*(n : ℝ)*t)*traceWindow (runWindow r (k+n)))
      atTop (𝓝 0) := by
  have hsum:=tendsto_finsetSum Finset.univ (fun i (_ : i∈(Finset.univ : Finset (Fin (H+2)))) =>
    discounted_norm_sq_tendsto_zero r.x hC hS hx (k-H+i.val))
  simpa only [runWindow,segmentWindow,HRun.segment,traceWindow,Matrix.trace,Matrix.diag_apply,
    Matrix.gram_apply,real_inner_self_eq_norm_sq,Finset.mul_sum,
    show ∀ n i : ℕ,k+n-H+i=n+(k-H+i) by omega,Finset.sum_const_zero] using hsum

/-- The terminal term is proved to vanish for every actual infinite H-segment. -/
theorem discounted_window_price_tendsto_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β t : ℝ} {H : ℕ} (hB : B≠0) (r : HRun E A B β H) (L : WindowPrice H)
    (hRate : growthRate A B β H<Real.exp t) (k : ℕ) (hk : H≤k) :
    Tendsto (fun n : ℕ => Real.exp (-2*(n : ℝ)*t)*L (runWindow r (k+n))) atTop (𝓝 0) := by
  have hlog : growthExponent A B β H<t:=Real.exp_lt_exp.mp hRate
  let S:=(growthExponent A B β H+t)/2
  have hS : S<t:=by dsimp [S]; linarith
  have hR : growthRate A B β H<Real.exp S:=by
    apply Real.exp_lt_exp.mpr
    dsimp [S]
    linarith
  obtain ⟨C,hC,hx⟩:=hRun_exists_norm_exp_bound hB r hR
  have htrace:=discounted_run_trace_tendsto_zero r hC hS hx k hk
  have hlim : Tendsto (fun n : ℕ => priceSize L*
      (Real.exp (-2*(n : ℝ)*t)*traceWindow (runWindow r (k+n)))) atTop (𝓝 0) :=by
    simpa only [mul_zero] using tendsto_const_nhds.mul htrace
  apply squeeze_zero_norm _ hlim
  intro n
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hY : runWindow r (k+n)∈windowCone A B β H:=
    segmentWindow_mem hB (r.segment (k+n)) (k+n) (by omega) le_rfl
  have hh:=mul_le_mul_of_nonneg_left (price_le_trace hY L) (Real.exp_pos (-2*(n : ℝ)*t)).le
  nlinarith

end polyak.FiniteHorizon
