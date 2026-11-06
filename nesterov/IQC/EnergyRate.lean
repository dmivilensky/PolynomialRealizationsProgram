import nesterov.Rates.Limit

/-!
Article: Lemma `lem:iqc`, the strict one-exponent conclusion.
Use: a uniform discounted energy estimate over genuine executions is upgraded
by restarting, without a second exponent or a stability hypothesis.
-/
namespace nesterov.IQC
noncomputable section
open Finset

def discountedState {M : StationaryMethod} {μ L : ℝ}
    (r : Rates.HilbertRun M μ L) (t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-2*(k:ℝ)*t)*r.stateNorm k^2

def UniformStateMassBound (M : StationaryMethod) (μ L t C : ℝ) : Prop :=
  ∀ r : Rates.HilbertRun M μ L,∀ N : ℕ,
    ∑ k∈range (N+1),discountedState r t k ≤ C*r.stateNorm 0^2

theorem discountedState_nonneg {M : StationaryMethod} {μ L : ℝ}
    (r : Rates.HilbertRun M μ L) (t : ℝ) (k : ℕ) : 0≤discountedState r t k :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem discountedState_shift {M : StationaryMethod} {μ L : ℝ}
    (r : Rates.HilbertRun M μ L) (t : ℝ) (k n : ℕ) :
    discountedState (r.shift k) t n = Real.exp (2*(k:ℝ)*t)*discountedState r t (k+n) := by
  simp only [discountedState,Rates.HilbertRun.stateNorm_shift,Nat.cast_add]
  rw [←mul_assoc,←Real.exp_add]
  congr 2
  ring

theorem discountedState_le_of_uniformMass {M : StationaryMethod} {μ L t C : ℝ}
    (h : UniformStateMassBound M μ L t C) (r : Rates.HilbertRun M μ L) (k : ℕ) :
    discountedState r t k≤C*r.stateNorm 0^2 :=
  (single_le_sum (fun j _ => discountedState_nonneg r t j)
    (mem_range.mpr (Nat.lt_succ_self k))).trans (h r k)

theorem discountedState_reverse_bound {M : StationaryMethod} {μ L t C : ℝ}
    (h : UniformStateMassBound M μ L t C) (r : Rates.HilbertRun M μ L)
    {k N : ℕ} (hk : k≤N) : discountedState r t N≤C*discountedState r t k := by
  have hh := discountedState_le_of_uniformMass h (r.shift k) (N-k)
  rw [discountedState_shift,Nat.add_sub_of_le hk] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*(k:ℝ)*t)).le
  have he : Real.exp (-2*(k:ℝ)*t)*Real.exp (2*(k:ℝ)*t)=1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [←mul_assoc,he,one_mul] at hm
  simp only [Rates.HilbertRun.stateNorm_shift,Nat.add_zero] at hm
  exact hm.trans_eq (by dsimp [discountedState]; ring)

/-- Restarting turns one finite-energy bound into an inverse-horizon gain. -/
theorem discountedState_horizon_bound {M : StationaryMethod} {μ L t C : ℝ}
    (hC : 0≤C) (h : UniformStateMassBound M μ L t C)
    (r : Rates.HilbertRun M μ L) (N : ℕ) :
    (N+1:ℝ)*discountedState r t N ≤ C^2*r.stateNorm 0^2 := by
  calc
    _ = ∑ _k∈range (N+1),discountedState r t N := by simp
    _ ≤ ∑ k∈range (N+1),C*discountedState r t k := by
      apply sum_le_sum
      intro k hk
      exact discountedState_reverse_bound h r (Nat.le_of_lt_succ (mem_range.mp hk))
    _ = C*(∑ k∈range (N+1),discountedState r t k) := (mul_sum _ _ _).symm
    _ ≤ C*(C*r.stateNorm 0^2) := mul_le_mul_of_nonneg_left (h r N) hC
    _ = _ := by ring

/-- A single exponent with a uniform energy bound lies strictly above the
actual all-Hilbert worst-case exponent. -/
theorem rate_lt_exp_of_uniformStateMassBound {M : StationaryMethod} {μ L t C : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hC : 0≤C) (h : UniformStateMassBound M μ L t C) :
    Rates.rate M μ L<Real.exp t := by
  obtain ⟨N,hN⟩ := exists_nat_gt (4*C^2+1)
  have hNp : 0<N := by exact_mod_cast (show (0:ℝ)<N by nlinarith [sq_nonneg C])
  have hbound (r : Rates.HilbertRun M μ L) :
      r.stateNorm N ≤ Real.exp ((N:ℝ)*t)/2*r.stateNorm 0 := by
    have hb := discountedState_horizon_bound hC h r N
    have hs : 0≤r.stateNorm 0 := M.stateNorm_nonneg r.w 0
    have hn : 0≤r.stateNorm N := M.stateNorm_nonneg r.w N
    have he : Real.exp ((N:ℝ)*t)^2*Real.exp (-2*(N:ℝ)*t)=1 := by
      rw [←Real.exp_nat_mul,←Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have hepos := Real.exp_pos ((N:ℝ)*t)
    have hwpos := Real.exp_pos (-2*(N:ℝ)*t)
    have hsq : 4*(Real.exp (-2*(N:ℝ)*t)*r.stateNorm N^2)≤r.stateNorm 0^2 := by
      dsimp [discountedState] at hb
      nlinarith [mul_nonneg (discountedState_nonneg r t N) (show 0≤(N:ℝ)+1-4*C^2 by linarith),
        mul_nonneg (sq_nonneg C) (sq_nonneg (r.stateNorm 0))]
    have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.exp ((N:ℝ)*t)))
    have hid : Real.exp ((N:ℝ)*t)^2*(4*(Real.exp (-2*(N:ℝ)*t)*r.stateNorm N^2))=
        4*r.stateNorm N^2 := by
      calc
        _ = 4*(Real.exp ((N:ℝ)*t)^2*Real.exp (-2*(N:ℝ)*t))*r.stateNorm N^2 := by ring
        _ = _ := by rw [he]; ring
    rw [hid] at hm
    have hsq2 : (2*r.stateNorm N)^2≤(Real.exp ((N:ℝ)*t)*r.stateNorm 0)^2 := by
      nlinarith only [hm]
    have hlin := (sq_le_sq₀ (by positivity : 0≤2*r.stateNorm N)
      (mul_nonneg hepos.le hs)).mp hsq2
    linarith
  have henv : Rates.envelope M μ L N≤Real.exp ((N:ℝ)*t)/2 := by
    apply csSup_le (Set.insert_nonempty _ _)
    intro x hx
    rcases hx with rfl | ⟨r,hr,rfl⟩
    · positivity
    · apply (div_le_iff₀ (lt_of_le_of_ne (M.stateNorm_nonneg r.w 0) (Ne.symm hr))).mpr
      exact hbound r
  by_contra hn
  have hr := pow_le_pow_left₀ (Real.exp_pos t).le (le_of_not_gt hn) N
  have hp := Rates.rate_pow_le_envelope M hμ hμL N
  have he : Real.exp t^N=Real.exp ((N:ℝ)*t) := (Real.exp_nat_mul t N).symm
  rw [he] at hr
  linarith [Real.exp_pos ((N:ℝ)*t)]

end
end nesterov.IQC
