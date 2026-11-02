import jacobi.Support.VolterraCosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The genuine complex support waves have uniform power growth on every
bounded scaled-energy disc about the physical edge one. In particular
the source's original real bound at one is unconditional.
Use: the original complex support edge limit has a proved actual uniform a priori bound; naturalPolynomial_one_bound supplies the final assertion of Appendix C.3.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual original support waves are uniformly bounded by their genuine growth power on every bounded complex n^(-2) edge disc about one.
Use: the original complex support edge limit has a proved actual uniform a priori bound; naturalPolynomial_one_bound supplies the final assertion of Appendix C.3.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the actual step has n*h tending to pi. The elementary cosine remainder bounds the true top-node displacement from one by gamma^2*h^2. On the original growing half chain, this gives a common bound for the actual Volterra scaled energy, so its proved global cosh estimate gives the original power bound. -/
theorem naturalWave_near_one {a b:ℝ} (ha:-1<a) (hb:-1<b) {R:ℝ} (hR:0≤R) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+4→∀y:ℂ,
      ‖y-1‖≤R/(n:ℝ)^2→‖naturalWave a b ha hb n m y‖≤C*((m:ℝ)+1)^gamma a := by
  -- The genuine energy disc is centered at the physical endpoint, while the exact Volterra equation uses its actual moving top node.
  obtain ⟨C,B,hC,hB,hbound⟩ := naturalWave_cosh ha hb
  let K := (gamma a)^2*(π+1)^2
  refine ⟨C*cosh (sqrt (B*(R+K))),mul_pos hC (cosh_pos _),?_⟩
  have hstep : ∀ᶠn:ℕ in atTop,(n:ℝ)*step a b (n+1)≤π+1 :=
    ((support_step_limit a b tendsto_id).eventually (Iio_mem_nhds (by linarith))).mono (fun _ h => h.le)
  filter_upwards [hbound,hstep,eventually_ge_atTop (8:ℕ)] with n hn hs hlarge
  intro m hm y hy
  let h := step a b (n+1)
  let x : ℝ := (m:ℝ)+1
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hx0 : 0≤x := by dsimp [x]; positivity
  have hxn : x≤n := by dsimp [x]; exact_mod_cast (show m+1≤n by omega)
  have hh : 0≤h := (step_pos ha hb (by omega)).le
  have hxh : 0≤x*h ∧ x*h≤π+1 :=
    ⟨mul_nonneg hx0 hh,(mul_le_mul_of_nonneg_right hxn hh).trans hs⟩
  have hcos : ‖(1:ℂ)-(cos (gamma a*h):ℝ)‖≤(gamma a*h)^2 := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (cos_le_one _))]
    nlinarith only [one_sub_sq_div_two_le_cos (x:=gamma a*h),sq_nonneg (gamma a*h)]
  have hdisp : ‖y-(cos (gamma a*h):ℝ)‖≤R/(n:ℝ)^2+(gamma a*h)^2 := by
    calc
      _ ≤ ‖y-1‖+‖(1:ℂ)-(cos (gamma a*h):ℝ)‖ := by
        have he : y-(cos (gamma a*h):ℝ)=(y-1)+((1:ℂ)-(cos (gamma a*h):ℝ)) := by ring
        rw [he]
        exact norm_add_le _ _
      _ ≤ _ := add_le_add hy hcos
  have hsmall : R/(n:ℝ)^2*x^2≤R := by
    calc
      _ = R*(x^2/(n:ℝ)^2) := by ring
      _ ≤ R*1 := mul_le_mul_of_nonneg_left
        ((div_le_one (sq_pos_of_pos hn0)).mpr ((sq_le_sq₀ hx0 hn0.le).mpr hxn)) hR
      _ = _ := mul_one _
  have hground : (gamma a*h)^2*x^2≤K := by
    have hh2 : (x*h)^2≤(π+1)^2 := (sq_le_sq₀ hxh.1 (by positivity)).mpr hxh.2
    calc
      _ = (gamma a)^2*(x*h)^2 := by ring
      _ ≤ K := mul_le_mul_of_nonneg_left hh2 (sq_nonneg (gamma a))
  have henergy : volterraEnergy a b n m y≤R+K := by
    have hscaled := mul_le_mul_of_nonneg_right hdisp (sq_nonneg x)
    change ‖y-(cos (gamma a*h):ℝ)‖*x^2≤R+K
    nlinarith only [hscaled,hsmall,hground]
  have hmajor : cosh (sqrt (B*volterraEnergy a b n m y))≤cosh (sqrt (B*(R+K))) := by
    apply cosh_le_cosh.mpr
    rw [abs_of_nonneg (sqrt_nonneg _),abs_of_nonneg (sqrt_nonneg _)]
    exact sqrt_le_sqrt (mul_le_mul_of_nonneg_left henergy hB.le)
  calc
    _ ≤ C*((m:ℝ)+1)^gamma a*cosh (sqrt (B*volterraEnergy a b n m y)) := hn m (by omega) y
    _ ≤ C*((m:ℝ)+1)^gamma a*cosh (sqrt (B*(R+K))) := mul_le_mul_of_nonneg_left hmajor (by positivity)
    _ = _ := by ring

/-- The genuine original support polynomial has the complete source power bound at the physical endpoint one.
Use: the original frequency envelope includes this exact endpoint assertion; support edge normalization uses the same actual polynomial family.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the actual zero-radius edge disc contains precisely one. The proved complex wave estimate is the same actual real polynomial evaluation there. -/
theorem naturalPolynomial_one_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+4→
      |(naturalPolynomial a b ha hb n m).eval 1|≤C*((m:ℝ)+1)^gamma a := by
  -- The actual complex value at the real endpoint is exactly the original real polynomial evaluation.
  obtain ⟨C,hC,hbound⟩ := naturalWave_near_one ha hb (R:=0) le_rfl
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with n hn
  intro m hm
  have h := hn m hm (1:ℂ) (by simp)
  have heq : naturalWave a b ha hb n m (1:ℝ)=(((naturalPolynomial a b ha hb n m).eval (1:ℝ):ℝ):ℂ) :=
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval _ _
  change ‖naturalWave a b ha hb n m (1:ℝ)‖≤_ at h
  rw [heq,Complex.norm_real,Real.norm_eq_abs] at h
  exact h

end
end jacobi.Support
