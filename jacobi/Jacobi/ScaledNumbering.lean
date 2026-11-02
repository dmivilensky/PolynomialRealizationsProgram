import jacobi.Jacobi.ScaledPhase

/-!
Article: jacobi, Proposition B.1.
The true scaled finite phase advances by exactly pi between consecutive
original Jacobi zeros once its actual restoring coefficient is positive.
The smooth original potential bound discharges that positivity throughout
the growing first-half interval. No asymptotic zero-level correspondence
is assumed.
Use: the finite phase comparison and actual zero expansions keep the original canonical index throughout.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original angular Jacobi zero in its genuine Bessel-scaled coordinate.
Use: the finite phase comparison and actual zero expansions keep the original canonical index throughout.
Article: jacobi, Proposition B.1.
-/
def scaledAngle (a b : ℝ) (ha : -1<a) (hb : -1<b) (n k : ℕ) : ℝ :=
  frequency a b n*finiteAngleAt a b ha hb n k

/-- The genuinely constructed scaled finite phase has exactly the original numbered pi levels on every actual large-argument compared nodal prefix.
Use: aligns the original finite Jacobi and Bessel zero phases in the uniform angular expansion of Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: the actual C1 potential bound and inverse-square Bessel restoring
bound make the true phase speed at least one quarter on the specified
original nodal interval. Every consecutive scaled original interval is
zero-free by actual finite zero exhaustion. The genuine phase increment
theorem therefore gives exactly pi per interval; induction adds them. -/
theorem scaledPhase_numbered_zero {a b C : ℝ} (ha : -1<a) (hb : -1<b)
    (hbound : ∀ t∈Icc 0 (3*Real.pi/4),|regularPotential a b t|≤C)
    {n k M : ℕ} (hK : k+M<n) (hN : 0<frequency a b n)
    (hNlarge : 4*C≤frequency a b n^2)
    (hbaseLarge : 2*(a^2+1)≤scaledAngle a b ha hb n k)
    (hcap : finiteAngleAt a b ha hb n (k+M)≤3*Real.pi/4) :
    scaledPhase a b ha hb n hN (scaledAngle a b ha hb n k)
      (scaledAngle a b ha hb n (k+M))=(M:ℝ)*Real.pi := by
  -- All zero-free intervals and every phase level below come from the same actual sorted finite polynomial zero list.
  let N := frequency a b n
  let Z := scaledAngle a b ha hb n
  let S := scaledState a b ha hb n hN
  have hk : k<n := by omega
  have hdomain := scaled_domain hN
  have hconv : Convex ℝ ((fun x : ℝ => x/N) ⁻¹' Ioo 0 Real.pi) := by rw [hdomain]; exact convex_Ioo _ _
  have hopen : IsOpen ((fun x : ℝ => x/N) ⁻¹' Ioo 0 Real.pi) := by rw [hdomain]; exact isOpen_Ioo
  have hphys : ∀ i : ℕ,i<n → Z i/N∈Ioo 0 Real.pi := by
    intro i hi
    dsimp [Z,scaledAngle,N]
    rw [mul_div_cancel_left₀ _ hN.ne']
    exact finiteAngleAt_interval ha hb hi
  have hzero : ∀ i : ℕ,i<n → S.value (Z i)=0 :=
    fun i hi => (scaledAngle_zero ha hb hN hi).2
  have hmono : ∀ i j : ℕ,i<j → j<n → Z i<Z j :=
    fun i j hij hj => mul_lt_mul_of_pos_left (finiteAngleAt_lt ha hb hij hj) hN
  have hmonole : ∀ i j : ℕ,i≤j → j<n → Z i≤Z j := by
    intro i j hij hj
    rcases hij.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (hmono i j hlt hj).le
  have hspeed : ∀ x∈Icc (Z k) (Z (k+M)),0<S.phaseDensity x := by
    intro x hx
    have hxlo : 2*(a^2+1)≤x := hbaseLarge.trans hx.1
    have hxp : 0<x := by nlinarith [sq_nonneg a]
    have htheta : x/N∈Icc 0 (3*Real.pi/4) := by
      refine ⟨(div_pos hxp hN).le,?_⟩
      have hh := (div_le_div_of_nonneg_right hx.2 hN.le).trans_eq (by
        change Z (k+M)/N=finiteAngleAt a b ha hb n (k+M)
        dsimp [Z,scaledAngle,N]
        exact mul_div_cancel_left₀ _ hN.ne')
      exact hh.trans hcap
    have hxe : x/N∈Ioo 0 Real.pi := ⟨div_pos hxp hN,by linarith [htheta.2,Real.pi_pos]⟩
    have he : -(1/4:ℝ)≤regularPotential a b (x/N)/N^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
      have hh := (abs_le.mp (hbound (x/N) htheta)).1
      change 4*C≤N^2 at hNlarge
      linarith
    have hq : (1/4:ℝ)≤S.potential x := by
      rw [scaledState_potential ha hb n hN hxp]
      have hh := jacobi.Bessel.wave_restoring_bound a hxlo
      change (1/2:ℝ)≤1+endpointCorrection a/x^2 at hh
      linarith
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (S.phaseDensity_lower hxe (by norm_num) hq)
  have hall : ∀ m≤M,S.phase (Z k) (Z (k+m))=(m:ℝ)*Real.pi := by
    intro m
    induction m with
    | zero => intro _; simp only [Nat.add_zero,RestoringSolution.phase_self,Nat.cast_zero,zero_mul]
    | succ m ih =>
      intro hm
      have hmK : k+m+1<n := by omega
      have hstep := S.phase_increment_between_zeros hopen hconv (hphys k hk) (hzero k hk)
        (hphys (k+m) (by omega)) (hphys (k+m+1) hmK)
        (hmono (k+m) (k+m+1) (by omega) hmK) (hzero (k+m) (by omega)) (hzero (k+m+1) hmK)
        (by
          intro x hx
          apply finiteAngleAt_no_zero_between ha hb hmK
          constructor
          · apply (lt_div_iff₀ hN).mpr
            simpa only [Z,scaledAngle,N,mul_comm] using hx.1
          · apply (div_lt_iff₀ hN).mpr
            simpa only [Z,scaledAngle,N,mul_comm] using hx.2)
        (by
          intro x hx
          apply hspeed x
          exact ⟨(hmonole k (k+m) (by omega) (by omega)).trans hx.1,
            hx.2.trans (hmonole (k+m+1) (k+M) (by omega) hK)⟩)
      rw [ih (by omega)] at hstep
      rw [show k+(m+1)=k+m+1 by omega]
      push_cast
      linarith
  exact hall M le_rfl

end
end jacobi.Jacobi
