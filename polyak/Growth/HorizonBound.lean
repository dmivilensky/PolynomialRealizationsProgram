import polyak.Growth.HorizonCertificate
import polyak.Growth.Prefactor
import polyak.FiniteHorizon.PricesLimit
import polyak.Growth.Original

/-!
Article: Appendix C, the constant-window estimate and the final finite-horizon upper bound.
Use: the price is evaluated on the actual Gram window, and its contraction is
required only on actual segment transitions. All constants are uniform in dimension,
the table and the horizon.
-/
namespace polyak.Growth.FiniteHorizon
noncomputable section
open Finset Filter
open polyak.FiniteHorizon
open scoped Topology

variable {A B β T : ℝ} {H : ℕ}

/-- The actual finite Gram-and-value window of an infinite H-table. -/
def _root_.polyak.Growth.HRun.window {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r : HRun E A B β H) (k : ℕ) : WindowSpace H :=
  segmentWindow (r.segment k) k

theorem _root_.polyak.Growth.HRun.window_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r : HRun E A B β H) (hB : B≠0) (k : ℕ) (hk : H≤k) :
    r.window k∈windowCone A B β H := segmentWindow_mem hB (r.segment k) k hk le_rfl

theorem _root_.polyak.Growth.HRun.trace_window {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (r : HRun E A B β H) (k : ℕ) (hk : H≤k) :
    traceWindow (r.window k)=windowTrace r.x H k := trace_segmentWindow (r.segment k) k hk

theorem _root_.polyak.Growth.HRun.window_transition {d : ℕ}
    (r : HRun (EuclideanSpace ℝ (Fin d)) A B β H) (k : ℕ) (hk : H≤k) :
    (r.window k,r.window (k+1))∈windowTransitions A B β H :=
  ⟨d,k+1,r.segment (k+1),k,hk,le_rfl,rfl,rfl⟩

/-- One finite constant controls every short discounted window growth. -/
theorem exists_short_window_bound (A B β T : ℝ) (H p : ℕ) :
    ∃ D : ℝ,1≤D ∧ ∀ d : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,
      ∀ k s : ℕ,H≤k → s≤p →
      windowTrace r.x H (k+s)≤D*Real.exp (2*(s : ℝ)*T)*windowTrace r.x H k := by
  let f : ℕ → ℝ := fun s => Real.exp (-2*(s : ℝ)*T)*(H+2 : ℝ)*windowFactor A B β H s
  have hfac (s : ℕ) : 0≤windowFactor A B β H s :=
    (sq_nonneg (envelope A B β H s)).trans
      (envelope_sq_le_windowFactor A B β (H:=H) (p:=s) (i:=s) (by omega) le_rfl)
  have hf (s : ℕ) : 0≤f s :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity)) (hfac s)
  let D:=1+∑ s∈range (p+1),f s
  have hD : 1≤D := le_add_of_nonneg_right (sum_nonneg fun s _ => hf s)
  refine ⟨D,hD,fun d r k s hk hs => ?_⟩
  have hfD : f s≤D := by
    have hh:=single_le_sum (fun j _ => hf j) (mem_range.mpr (by omega : s<p+1))
    dsimp only [D]
    linarith
  have he : Real.exp (-2*(s : ℝ)*T)*Real.exp (2*(s : ℝ)*T)=1 := by
    rw [←Real.exp_add]
    have hz : -2*(s : ℝ)*T+2*(s : ℝ)*T=0 := by ring
    rw [hz,Real.exp_zero]
  have hcoef : (H+2 : ℝ)*windowFactor A B β H s≤D*Real.exp (2*(s : ℝ)*T) := by
    have hh:=mul_le_mul_of_nonneg_right hfD (Real.exp_pos (2*(s : ℝ)*T)).le
    have heq : f s*Real.exp (2*(s : ℝ)*T)=(H+2 : ℝ)*windowFactor A B β H s := by
      calc
        _ = (Real.exp (-2*(s : ℝ)*T)*Real.exp (2*(s : ℝ)*T))*
          ((H+2 : ℝ)*windowFactor A B β H s) := by dsimp [f]; ring
        _ = _ := by rw [he,one_mul]
    rwa [heq] at hh
  exact (windowTrace_add_le (r.segment (k+s)) k s hk le_rfl).trans
    (mul_le_mul_of_nonneg_right hcoef (windowTrace_nonneg r.x H k))

/-- The concrete near-kernel estimate needed by the final good/bad-window argument. -/
def NearKernelBound (A B β T : ℝ) (H p : ℕ) (η : ℝ) (L : WindowPrice H) : Prop :=
  ∀ d n : ℕ,∀ s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,
    ∀ k : ℕ,H≤k → k+p≤n →
      L (segmentWindow s k)≤η*windowTrace s.x H k →
      windowTrace s.x H (k+p)≤Real.exp (2*(p : ℝ)*T)*windowTrace s.x H k/2

/-- The constant-window estimate on every infinite admissible table, with every
price and short-growth hypothesis discharged on the genuine Gram windows. -/
theorem exists_window_prefactor (hB : B≠0) (L : WindowPrice H)
    (hprice : PriceContracts A B β H T L) {p : ℕ} {η : ℝ}
    (hp : 0<p) (hη : 0<η) (hnear : NearKernelBound A B β T H p η L) :
    ∃ C : ℝ,0<C ∧ ∀ d : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,
      ∀ k : ℕ,windowTrace r.x H (H+k)≤C*Real.exp (2*(k : ℝ)*T)*windowTrace r.x H H := by
  obtain ⟨D,hD,hshort⟩:=exists_short_window_bound A B β T H p
  let C:=max D (D*priceSize L/η)
  have hC : 0<C := zero_lt_one.trans_le (hD.trans (le_max_left _ _))
  refine ⟨C,hC,fun d r k => ?_⟩
  let w : ℕ → ℝ := fun i => windowTrace r.x H (H+i)
  let v : ℕ → ℝ := fun i => L (r.window (H+i))
  have hexp (i : ℕ) : (Real.exp T)^(2*i)=Real.exp (2*(i : ℝ)*T) := by
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hv0 : v 0≤priceSize L*w 0 := by
    have hh:=price_le_trace (r.window_mem hB H le_rfl) L
    rw [r.trace_window H le_rfl] at hh
    exact (le_abs_self _).trans hh
  have hv : ∀ i,v (i+1)≤(Real.exp T)^2*v i := by
    intro i
    have hh:=hprice _ (r.window_transition (H+i) (by omega))
    have he : Real.exp (2*T)=(Real.exp T)^2 := by
      rw [show 2*T=T+T by ring,Real.exp_add,pow_two]
    simpa only [v,Nat.add_assoc,he] using hh
  have hs : ∀ i s : ℕ,s≤p → w (i+s)≤D*(Real.exp T)^(2*s)*w i := by
    intro i s hs
    simpa only [w,Nat.add_assoc,hexp] using hshort d r (H+i) s (by omega) hs
  have hb : ∀ i,v i≤η*w i → w (i+p)≤(Real.exp T)^(2*p)*w i/2 := by
    intro i hi
    have hh:=hnear d (H+i+p) (r.segment (H+i+p)) (H+i) (by omega) le_rfl hi
    simpa only [w,HRun.segment,Nat.add_assoc,hexp] using hh
  simpa only [w,hexp,C,Nat.add_zero] using weighted_window_bound
    (fun i => windowTrace_nonneg r.x H (H+i)) (Real.exp_pos T) (priceSize_nonneg L)
    hD hη hp hv0 hv hs hb k

/-- A uniform bound on the actual Gram windows controls the full exact envelope,
including the finitely many initial horizons and every zero initial state. -/
theorem envelope_prefactor_of_window_bound {C : ℝ} (hC : 0<C)
    (hwindow : ∀ d : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,
      ∀ k : ℕ,windowTrace r.x H (H+k)≤C*Real.exp (2*(k : ℝ)*T)*windowTrace r.x H H) :
    ∃ D : ℝ,0<D ∧ ∀ n : ℕ,envelope A B β H n≤D*Real.exp ((n : ℝ)*T) := by
  let M:=1+∑ k∈Icc 0 (H+1),envelope A B β H k^2
  have hM : 0<M := by
    have hh : 0≤∑ k∈Icc 0 (H+1),envelope A B β H k^2 := sum_nonneg fun _ _ => sq_nonneg _
    dsimp only [M]
    linarith
  let P:=∑ k∈range H,envelope A B β H k^2*Real.exp (-2*(k : ℝ)*T)
  have hP : 0≤P := sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  let D:=1+C*M*Real.exp (-2*(H : ℝ)*T)+P
  have hD : 0<D := by dsimp only [D]; positivity
  have hinitial {d : ℕ} (r : HRun (EuclideanSpace ℝ (Fin d)) A B β H) :
      windowTrace r.x H H≤M*stateNorm r.x 0^2 := by
    have hterm (k : ℕ) : ‖r.x k‖^2≤envelope A B β H k^2*stateNorm r.x 0^2 := by
      have hh:=(sq_le_sq₀ (norm_nonneg _) (mul_nonneg (envelope_nonneg A B β H k)
        (stateNorm_nonneg r.x 0))).mpr (r.norm_le_envelope k)
      simpa only [mul_pow] using hh
    calc
      _ = ∑ k∈Icc 0 (H+1),‖r.x k‖^2 := by rw [windowTrace,Nat.sub_self]
      _ ≤ ∑ k∈Icc 0 (H+1),envelope A B β H k^2*stateNorm r.x 0^2 :=
        sum_le_sum fun k _ => hterm k
      _ = (∑ k∈Icc 0 (H+1),envelope A B β H k^2)*stateNorm r.x 0^2 := (sum_mul _ _ _).symm
      _ ≤ M*stateNorm r.x 0^2 := by dsimp only [M]; nlinarith [sq_nonneg (stateNorm r.x 0)]
  have hstate {d : ℕ} (r : HRun (EuclideanSpace ℝ (Fin d)) A B β H) (n : ℕ) :
      stateNorm r.x n^2≤D*Real.exp (2*(n : ℝ)*T)*stateNorm r.x 0^2 := by
    by_cases hn : H≤n
    · have hwin:=hwindow d r (n-H)
      rw [Nat.add_sub_of_le hn] at hwin
      have hexp : Real.exp (2*((n-H : ℕ) : ℝ)*T)=
          Real.exp (-2*(H : ℝ)*T)*Real.exp (2*(n : ℝ)*T) := by
        rw [←Real.exp_add,Nat.cast_sub hn]
        congr 1
        ring
      have hcoef : C*M*Real.exp (-2*(H : ℝ)*T)≤D := by dsimp only [D]; linarith
      calc
        _ ≤ windowTrace r.x H n := stateNorm_sq_le_windowTrace r.x H n
        _ ≤ C*Real.exp (2*((n-H : ℕ) : ℝ)*T)*(M*stateNorm r.x 0^2) :=
          hwin.trans (mul_le_mul_of_nonneg_left (hinitial r) (by positivity))
        _ = (C*M*Real.exp (-2*(H : ℝ)*T))*Real.exp (2*(n : ℝ)*T)*stateNorm r.x 0^2 := by
          rw [hexp]
          ring
        _ ≤ _ := by gcongr
    · have hterm : envelope A B β H n^2*Real.exp (-2*(n : ℝ)*T)≤P := by
        dsimp only [P]
        exact single_le_sum (f:=fun k : ℕ => envelope A B β H k^2*Real.exp (-2*(k : ℝ)*T))
          (fun k _ => mul_nonneg (sq_nonneg (envelope A B β H k)) (Real.exp_pos _).le)
          (mem_range.mpr (show n<H by omega))
      have hPD : P≤D := by
        have hh : 0≤C*M*Real.exp (-2*(H : ℝ)*T) := by positivity
        dsimp only [D]
        linarith
      have he : Real.exp (-2*(n : ℝ)*T)*Real.exp (2*(n : ℝ)*T)=1 := by
        rw [←Real.exp_add]
        have hz : -2*(n : ℝ)*T+2*(n : ℝ)*T=0 := by ring
        rw [hz,Real.exp_zero]
      have hcoef : envelope A B β H n^2≤D*Real.exp (2*(n : ℝ)*T) := by
        have hh:=mul_le_mul_of_nonneg_right (hterm.trans hPD) (Real.exp_pos (2*(n : ℝ)*T)).le
        rwa [mul_assoc,he,mul_one] at hh
      have hs:=stateNorm_le_envelope_hilbert (r.segment n)
      have hsq:=(sq_le_sq₀ (stateNorm_nonneg r.x n)
        (mul_nonneg (envelope_nonneg A B β H n) (stateNorm_nonneg r.x 0))).mpr hs
      rw [mul_pow] at hsq
      exact hsq.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  refine ⟨Real.sqrt D,Real.sqrt_pos.mpr hD,fun n => ?_⟩
  apply csSup_le (Set.insert_nonempty _ _)
  rintro v (rfl | ⟨d,s,hs,rfl⟩)
  · positivity
  · obtain ⟨r,hr,_⟩:=s.exists_hRun
    have hstates (k : ℕ) (hk : k≤n) : stateNorm r.x k=stateNorm s.x k := by
      simp only [stateNorm,hr k (by omega),hr (k+1) (by omega)]
    have hh:=hstate r n
    rw [hstates n le_rfl,hstates 0 (Nat.zero_le _)] at hh
    have he : Real.exp (2*(n : ℝ)*T)=Real.exp ((n : ℝ)*T)^2 := by
      rw [show 2*(n : ℝ)*T=(n : ℝ)*T+(n : ℝ)*T by ring,Real.exp_add,pow_two]
    have hsq : stateNorm s.x n^2≤(Real.sqrt D*Real.exp ((n : ℝ)*T)*stateNorm s.x 0)^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hD.le]
      rwa [he] at hh
    have hn:=(sq_le_sq₀ (stateNorm_nonneg s.x n)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
        (stateNorm_nonneg s.x 0))).mp hsq
    exact (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).mpr hn

/-- The final exact-rate envelope bound, with a genuine uniform constant. -/
theorem exists_envelope_prefactor (hB : B≠0) (L : WindowPrice H)
    (hprice : PriceContracts A B β H T L) {p : ℕ} {η : ℝ}
    (hp : 0<p) (hη : 0<η) (hnear : NearKernelBound A B β T H p η L) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope A B β H n≤C*Real.exp ((n : ℝ)*T) := by
  obtain ⟨C,hC,hwindow⟩:=exists_window_prefactor hB L hprice hp hη hnear
  exact envelope_prefactor_of_window_bound hC hwindow

/-- The actual original from-rest finite-horizon supremum has the same uniform
constant; dimensions, functions and horizons are all quantified by worstAll. -/
theorem exists_original_prefactor (μ L α β T : ℝ) {H : ℕ}
    (hB : Dynamics.normalizedB μ L α≠0) (price : WindowPrice H)
    (hprice : PriceContracts (Dynamics.normalizedA μ L α β)
      (Dynamics.normalizedB μ L α) β H T price) {p : ℕ} {η : ℝ}
    (hp : 0<p) (hη : 0<η)
    (hnear : NearKernelBound (Dynamics.normalizedA μ L α β)
      (Dynamics.normalizedB μ L α) β T H p η price) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,Dynamics.worstAll μ L α β n≤C*Real.exp ((n : ℝ)*T) := by
  obtain ⟨C,hC,hbound⟩:=exists_envelope_prefactor hB price hprice hp hη hnear
  refine ⟨Real.sqrt 2*C,by positivity,fun n => ?_⟩
  calc
    _ ≤ Real.sqrt 2*Growth.envelope (Dynamics.normalizedA μ L α β)
        (Dynamics.normalizedB μ L α) β n := Growth.worstAll_le_envelope μ L α β n
    _ ≤ Real.sqrt 2*envelope (Dynamics.normalizedA μ L α β)
        (Dynamics.normalizedB μ L α) β H n :=
      mul_le_mul_of_nonneg_left (full_envelope_le _ _ _ H n) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2*(C*Real.exp ((n : ℝ)*T)) :=
      mul_le_mul_of_nonneg_left (hbound n) (Real.sqrt_nonneg _)
    _ = _ := by ring

end
end polyak.Growth.FiniteHorizon
