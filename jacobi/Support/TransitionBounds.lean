import jacobi.Support.VolterraEstimates
import jacobi.Complex.TrigonometricRemainders

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The actual support polynomial and its actual first difference have
their original growth powers wherever (m+1)*|theta| is bounded.
This supplies the genuine starting state for oscillatory propagation.
Use: the global frequency envelope starts its genuine oscillatory free-state propagation at floor(1/|theta|), and also covers every earlier low-frequency index directly.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual support wave and its first physical difference have the source's full transition-region growth bounds.
Use: the global frequency envelope starts its genuine oscillatory free-state propagation at floor(1/|theta|), and also covers every earlier low-frequency index directly.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the original bounded scaled frequency gives a uniform bound for the actual Volterra energy by the genuine complex quadratic cosine remainder and n*h->pi. Apply the complete original global cosh wave and first-difference estimates, and add the proved actual top-node first difference. -/
theorem naturalWave_transition {a b R:ℝ} (ha:-1<a) (hb:-1<b) (hR:0≤R) :
    ∃A:ℝ,0<A ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+3→∀theta:ℂ,‖theta‖*((m:ℝ)+1)≤R→
      ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤A*((m:ℝ)+1)^gamma a ∧
      ‖naturalWave a b ha hb n (m+1) (Complex.cos theta)-naturalWave a b ha hb n m (Complex.cos theta)‖≤
        A*((m:ℝ)+1)^(gamma a-1) := by
  -- The same true moving top node, original spectral polynomial and actual lattice step determine the bounded Volterra energy.
  obtain ⟨C,B,hC,hB,hvolt⟩ := volterra_estimates ha hb
  obtain ⟨D,hD,htop⟩ := topValue_difference ha hb
  let K := (2*(exp R)^2)*R^2+(gamma a)^2*(π+1)^2
  let H := cosh (sqrt (B*K))
  have hK : 0≤K := by dsimp [K]; positivity
  have hH : 0<H := cosh_pos _
  let A := C*H+C*K*H+D
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  have hstep : ∀ᶠn:ℕ in atTop,(n:ℝ)*step a b (n+1)≤π+1 :=
    ((support_step_limit a b tendsto_id).eventually (Iio_mem_nhds (by linarith))).mono (fun _ h => h.le)
  filter_upwards [hvolt,htop,hstep,eventually_ge_atTop (8:ℕ)] with n hv hd hs hlarge
  intro m hm theta htheta
  let x : ℝ := (m:ℝ)+1
  let hh := step a b (n+1)
  let y := Complex.cos theta
  have hx : 0<x := by dsimp [x]; positivity
  have hx1 : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg m (α:=ℝ)]
  have hxn : x≤n := by dsimp [x]; exact_mod_cast (show m+1≤n by omega)
  have hh0 : 0≤hh := (step_pos ha hb (by omega)).le
  have hxh : 0≤x*hh ∧ x*hh≤π+1 :=
    ⟨mul_nonneg hx.le hh0,(mul_le_mul_of_nonneg_right hxn hh0).trans hs⟩
  have htR : ‖theta‖≤R := by nlinarith only [htheta,hx1,norm_nonneg theta]
  have hcos : ‖y-1‖≤(2*(exp R)^2)*‖theta‖^2 := jacobi.Complex.cosine_quadratic_bound hR htR
  have hground : ‖(1:ℂ)-(cos (gamma a*hh):ℝ)‖≤(gamma a*hh)^2 := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (cos_le_one _))]
    nlinarith only [one_sub_sq_div_two_le_cos (x:=gamma a*hh),sq_nonneg (gamma a*hh)]
  have henergy : volterraEnergy a b n m y≤K := by
    have hdisp : ‖y-(cos (gamma a*hh):ℝ)‖≤(2*(exp R)^2)*‖theta‖^2+(gamma a*hh)^2 := by
      have ht := dist_triangle y (1:ℂ) (cos (gamma a*hh):ℝ)
      simp only [dist_eq_norm] at ht
      exact ht.trans (add_le_add hcos hground)
    have hθsq := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hx.le) hR).mpr htheta
    have hhsq := (sq_le_sq₀ hxh.1 (by positivity)).mpr hxh.2
    have hθ := mul_le_mul_of_nonneg_left hθsq (by positivity : 0≤2*(exp R)^2)
    have hh' := mul_le_mul_of_nonneg_left hhsq (sq_nonneg (gamma a))
    have hscaled := mul_le_mul_of_nonneg_right hdisp (sq_nonneg x)
    change ‖y-(cos (gamma a*hh):ℝ)‖*x^2≤K
    dsimp [K]
    nlinarith only [hscaled,hθ,hh']
  have hmajor : cosh (sqrt (B*volterraEnergy a b n m y))≤H := by
    apply cosh_le_cosh.mpr
    rw [abs_of_nonneg (sqrt_nonneg _),abs_of_nonneg (sqrt_nonneg _)]
    exact sqrt_le_sqrt (mul_le_mul_of_nonneg_left henergy hB.le)
  have hcoeff : C*H≤A ∧ C*K*H+D≤A := by
    dsimp [A]
    constructor <;> linarith only [hD,mul_nonneg (mul_nonneg hC.le hK) hH.le,mul_pos hC hH]
  constructor
  · calc
      _ ≤ C*x^gamma a*cosh (sqrt (B*volterraEnergy a b n m y)) := (hv.1 m (by omega) y).1
      _ ≤ C*x^gamma a*H := mul_le_mul_of_nonneg_left hmajor (by positivity)
      _ = (C*H)*x^gamma a := by ring
      _ ≤ A*x^gamma a := mul_le_mul_of_nonneg_right hcoeff.1 (rpow_pos_of_pos hx _).le
  · let delta := naturalWave a b ha hb n (m+1) y-naturalWave a b ha hb n m y
    let u : ℂ := (topValue a b ha hb n (m+1):ℂ)-topValue a b ha hb n m
    have hu : ‖u‖≤D*x^(gamma a-1) := by
      dsimp only [u]
      rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      exact hd m (by omega)
    have herr := hv.2 m (by omega) y
    have hE : 0≤volterraEnergy a b n m y := by unfold volterraEnergy; positivity
    calc
      _ ≤ ‖delta-u‖+‖u‖ := by simpa only [sub_add_cancel] using norm_add_le (delta-u) u
      _ ≤ C*volterraEnergy a b n m y*x^(gamma a-1)*cosh (sqrt (B*volterraEnergy a b n m y))+D*x^(gamma a-1) := add_le_add herr hu
      _ ≤ C*K*x^(gamma a-1)*H+D*x^(gamma a-1) := by
        apply add_le_add _ le_rfl
        exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left henergy hC.le)
          (rpow_pos_of_pos hx _).le) hmajor (cosh_pos _).le (by positivity)
      _ = (C*K*H+D)*x^(gamma a-1) := by ring
      _ ≤ A*x^(gamma a-1) := mul_le_mul_of_nonneg_right hcoeff.2 (rpow_pos_of_pos hx _).le

end
end jacobi.Support
