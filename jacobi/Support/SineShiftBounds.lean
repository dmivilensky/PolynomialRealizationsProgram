import jacobi.Support.SinePowerBounds

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
Original shifted lattice sines are uniformly comparable to m*h on every
printed growing half-chain range. The shifts may be negative; their
actual positivity is accounted for by the genuine condition p>-1.
The constants come from the earlier proved smooth log-sinc bounds.
Use: shifted_sine_bounds supplies the genuine positive support denominators and uniform coefficient estimates on the entire growing half chain.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter chebyshev1.SineJacobi
open scoped Topology

/-- On every fixed compact positive half-period, the genuine sine is uniformly comparable with its actual angle, including the zero endpoint.
Use: shifted_sine_bounds supplies the genuine positive support denominators and uniform coefficient estimates on the entire growing half chain.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: the actual log-sinc has the proved uniform bound. Exponentiate both sides and multiply by the original nonnegative angle, using its exact sinc identity. -/
theorem sine_compact_bounds {b : ℝ} (hb:0≤b) (hb1:b<1) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀x∈Icc (0:ℝ) b,c*(π*x)≤sin (π*x) ∧ sin (π*x)≤C*(π*x) := by
  -- Positivity of the original sinc fixes both exponential inequalities at every actual point.
  obtain ⟨L,hL,hbound⟩ := logSinc_bound hb hb1
  refine ⟨exp (-L),exp L,exp_pos _,exp_pos _,?_⟩
  intro x hx
  have hs := sinc_pi_pos (show x∈Ioo (-1:ℝ) 1 from ⟨by linarith [hx.1],hx.2.trans_lt hb1⟩)
  have hlog := hbound x hx
  have hlo : exp (-L)≤sinc (π*x) := by
    rw [← exp_log hs]
    exact exp_le_exp.mpr (abs_le.mp hlog).1
  have hhi : sinc (π*x)≤exp L := by
    rw [← exp_log hs]
    exact exp_le_exp.mpr (abs_le.mp hlog).2
  have hsin : sin (π*x)=(π*x)*sinc (π*x) := by
    by_cases hzero:π*x=0
    · simp [hzero]
    · rw [sinc_of_ne_zero hzero,mul_div_cancel₀ _ hzero]
  rw [hsin]
  have hx0 : 0≤π*x := mul_nonneg pi_pos.le hx.1
  exact ⟨by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlo hx0,
    by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hhi hx0⟩

/-- Every original shifted support lattice sine is uniformly comparable with m*h in the full original growing half-chain range.
Use: diagonal_bounds and coupling_bounds control the actual support coefficients; top-node growth and difference estimates use the same genuine shifted sine factors.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: p>-1 makes m+p comparable with m at every actual positive index, including m=1. For sufficiently large original degree, every permitted shifted angle lies in [0,3*pi/4]. Apply the proved compact sine comparison and multiply the exact coordinate bounds by the genuine positive lattice step. -/
theorem shifted_sine_bounds (a b : ℝ) {p : ℝ} (hp:-1<p) (d : ℕ) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,0<step a b n ∧
      ∀m:ℕ,0<m→2*m≤n+d→
        c*(m:ℝ)*step a b n≤sin (((m:ℝ)+p)*step a b n) ∧
        sin (((m:ℝ)+p)*step a b n)≤C*(m:ℝ)*step a b n := by
  -- The single degree threshold covers every actual growing row, without a separate finite-prefix numerical argument.
  obtain ⟨c,C,hc,hC,hcomp⟩ := sine_compact_bounds (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3:ℝ)/4<1)
  let l : ℝ := min 1 (1+p)
  let u : ℝ := 1+|p|
  have hl : 0<l := lt_min (by norm_num) (by linarith)
  have hu : 0<u := by dsimp [u]; positivity
  refine ⟨c*l,C*u,mul_pos hc hl,mul_pos hC hu,?_⟩
  let v : ℝ := (a+b+1)/2
  let B : ℝ := 100+2*d+10*|v|+10*|p|
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_ge_atTop B)
  filter_upwards [he] with n hn
  have hv0 := neg_abs_le v
  have hv1 := le_abs_self v
  have hp0 := neg_abs_le p
  have hp1 := le_abs_self p
  have hd0 := Nat.cast_nonneg d (α:=ℝ)
  have hf : jacobi.Jacobi.frequency a b n=(n:ℝ)+v := rfl
  have hf0 : 0< jacobi.Jacobi.frequency a b n := by rw [hf]; dsimp [B] at hn; linarith
  have hh : 0<step a b n := div_pos pi_pos hf0
  refine ⟨hh,?_⟩
  intro m hm hmn
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hmr : 2*(m:ℝ)≤(n:ℝ)+d := by exact_mod_cast hmn
  have hlo : l*(m:ℝ)≤(m:ℝ)+p := by
    dsimp [l]
    by_cases hp':0≤p
    · rw [min_eq_left (by linarith : (1:ℝ)≤1+p)]
      linarith
    · rw [min_eq_right (by linarith : 1+p≤(1:ℝ))]
      nlinarith
  have hhi : (m:ℝ)+p≤u*(m:ℝ) := by dsimp [u]; nlinarith [abs_nonneg p]
  have hx0 : 0≤((m:ℝ)+p)/ jacobi.Jacobi.frequency a b n := div_nonneg (by linarith) hf0.le
  have hx1 : ((m:ℝ)+p)/ jacobi.Jacobi.frequency a b n≤(3:ℝ)/4 := by
    apply (div_le_iff₀ hf0).mpr
    rw [hf]
    dsimp [B] at hn
    linarith
  obtain ⟨hc',hC'⟩ := hcomp _ ⟨hx0,hx1⟩
  have harg : π*(((m:ℝ)+p)/ jacobi.Jacobi.frequency a b n)=((m:ℝ)+p)*step a b n := by dsimp [step]; ring
  rw [harg] at hc' hC'
  constructor
  · calc
      _ = c*(l*(m:ℝ))*step a b n := by ring
      _ ≤ c*((m:ℝ)+p)*step a b n := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlo hc.le) hh.le
      _ = c*(((m:ℝ)+p)*step a b n) := by ring
      _ ≤ _ := hc'
  · calc
      _ ≤ C*(((m:ℝ)+p)*step a b n) := hC'
      _ ≤ C*(u*(m:ℝ))*step a b n := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hC.le) hh.le
      _ = _ := by ring

end
end jacobi.Support
