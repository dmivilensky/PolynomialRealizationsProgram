import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The quadratic substitution maps the first quadrant to that half-plane,
so both boundary rays use the same imaginary-axis estimate.
Source: the Phragmen--Lindelof principle, mathlib's quadrant theorem.
Use: halfPlane_bound reduces the full closed-half-plane maximum bound to the standard quadrant Phragmen--Lindelof theorem.
-/
namespace jacobi.Complex
noncomputable section
open Real Set Filter Asymptotics Bornology _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every point of the closed right half-plane has a first-quadrant preimage under w maps to -i*w^2.
Use: halfPlane_bound reduces the full closed-half-plane maximum bound to the standard quadrant Phragmen--Lindelof theorem.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: a square root of i*z has real and imaginary parts with nonnegative product. One of the two opposite roots therefore lies in the first quadrant. -/
theorem halfPlane_square_preimage {z : ℂ} (hz : 0≤z.re) :
    ∃ w : ℂ,0≤w.re ∧ 0≤w.im ∧ -Complex.I*w^2=z := by
  -- The root choice is used only algebraically, so no square-root branch is differentiated.
  let w := Complex.sqrt (Complex.I*z)
  have hw : w^2=Complex.I*z := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ)≠0)
  have hi := congrArg Complex.im hw
  simp only [pow_two,mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] at hi
  have hp : 0≤w.re*w.im := by linarith
  have he : -Complex.I*w^2=z := by rw [hw]; simp [← mul_assoc]
  by_cases hr : 0≤w.re
  · by_cases hm : 0≤w.im
    · exact ⟨w,hr,hm,he⟩
    · have hre : w.re=0 := by nlinarith
      exact ⟨-w,by simp [hre],by simpa using (le_of_lt (neg_pos.mpr (lt_of_not_ge hm))),by simpa using he⟩
  · have hm : w.im≤0 := by nlinarith
    exact ⟨-w,by simpa using (le_of_lt (neg_pos.mpr (lt_of_not_ge hr))),by simpa using (neg_nonneg.mpr hm),by simpa using he⟩

/-- Polynomial growth and an imaginary-axis bound imply the same bound on the entire closed right half-plane.
Use: applied to the actual normalized Gamma quotient, this transfers its proved negative-energy boundary asymptotics to the uniform complex-frequency estimate required for Delta_tau.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the Phragmen--Lindelof principle in a quadrant.
Proof: compose with -i*w^2. Both quadrant rays map to the imaginary axis, polynomial growth is smaller than exp(norm(w)), and the quadrant theorem applies; every right-half-plane point has such a preimage. -/
theorem halfPlane_bound {f : ℂ → ℂ} {C B : ℝ} {n : ℕ}
    (hf : ∀ z : ℂ,0≤z.re → DifferentiableAt ℂ f z)
    (hB : 0≤B) (hg : ∀ z : ℂ,0≤z.re → ‖f z‖≤B*(1+‖z‖)^n)
    (hb : ∀ y : ℝ,‖f (Complex.I*(y:ℂ))‖≤C)
    {z : ℂ} (hz : 0≤z.re) : ‖f z‖≤C := by
  -- Squaring doubles polynomial degree but still leaves subexponential growth in the quadrant.
  let g : ℂ → ℂ := fun w => -Complex.I*w^2
  have hgre (w : ℂ) : (g w).re=2*w.re*w.im := by simp [g,pow_two,mul_re,mul_im]; ring
  have hclosed (w : ℂ) (hw : w∈closure (Ioi (0:ℝ) ×ℂ Ioi (0:ℝ))) : 0≤(g w).re := by
    rw [Complex.closure_reProdIm,closure_Ioi,Complex.mem_reProdIm] at hw
    rw [hgre]
    exact mul_nonneg (mul_nonneg (by norm_num) hw.1) hw.2
  have hd : DiffContOnCl ℂ (f ∘ g) (Ioi (0:ℝ) ×ℂ Ioi (0:ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    exact ((hf (g w) (hclosed w hw)).comp w (by dsimp [g]; fun_prop)).differentiableWithinAt
  have hpoly : (f ∘ g) =O[cobounded ℂ ⊓ 𝓟 (Ioi (0:ℝ) ×ℂ Ioi (0:ℝ))]
      (fun w : ℂ => ‖w‖^(2*n)) := by
    apply Asymptotics.IsBigO.of_bound (B*2^n)
    filter_upwards [(eventually_cobounded_le_norm (E := ℂ) 1).filter_mono inf_le_left,
      show ∀ᶠ w in cobounded ℂ ⊓ 𝓟 (Ioi (0:ℝ) ×ℂ Ioi (0:ℝ)),
        w∈Ioi (0:ℝ) ×ℂ Ioi (0:ℝ) from Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun _ h => h))]
      with w hw hQ
    have hwr : 0≤(g w).re := by rw [hgre]; exact mul_nonneg (mul_nonneg (by norm_num) hQ.1.le) hQ.2.le
    have hn : ‖g w‖=‖w‖^2 := by simp [g,norm_pow]
    have hp : (1+‖w‖^2)^n≤(2*‖w‖^2)^n := pow_le_pow_left₀ (by positivity) (by nlinarith) n
    simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤‖w‖^(2*n))]
    exact (hg (g w) hwr).trans (by rw [hn]; exact (mul_le_mul_of_nonneg_left hp hB).trans_eq (by rw [mul_pow,← pow_mul]; ring))
  have hexp : (fun w : ℂ => ‖w‖^(2*n)) =O[cobounded ℂ] (fun w => Real.exp ‖w‖) :=
    (Real.isLittleO_pow_exp_atTop (n := 2*n)).isBigO.comp_tendsto tendsto_norm_cobounded_atTop
  obtain ⟨w,hwr,hwi,hw⟩ := halfPlane_square_preimage hz
  have hb₁ (x : ℝ) (_hx : 0≤x) : ‖(f ∘ g) (x:ℂ)‖≤C := by
    change ‖f (g (x:ℂ))‖≤C
    rw [show g (x:ℂ)=Complex.I*((-x^2:ℝ):ℂ) by dsimp [g]; push_cast; ring]
    exact hb _
  have hb₂ (x : ℝ) (_hx : 0≤x) : ‖(f ∘ g) ((x:ℂ)*Complex.I)‖≤C := by
    change ‖f (g ((x:ℂ)*Complex.I))‖≤C
    rw [show g ((x:ℂ)*Complex.I)=Complex.I*((x^2:ℝ):ℂ) by dsimp [g]; push_cast; simp [mul_pow,Complex.I_sq]]
    exact hb _
  have h := PhragmenLindelof.quadrant_I hd
    ⟨1,by norm_num,1,by simpa using hpoly.trans (hexp.mono inf_le_left)⟩ hb₁ hb₂ hwr hwi
  simpa only [Function.comp_apply,g,hw] using h

end
end jacobi.Complex
