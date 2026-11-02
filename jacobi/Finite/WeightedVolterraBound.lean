import jacobi.Finite.PrefixGronwall
import jacobi.Finite.WeightedVolterraInequality

/-!
Article: jacobi, Appendix D.
A finite complex Volterra equation with the genuine weighted linear
kernel bound has a uniform exponential bound on its energy-scaled
prefix. The actual support application discharges every hypothesis
with its original polynomial, kernel and positive growth weight.
Source: finite-prefix discrete Gronwall inequality.
Use: Support.naturalWave_exponential supplies the actual original support spectral wave, reference solution, kernel and growth weight. Bounded scaled energies then give precisely the uniform a priori bounds needed by the original edge limit and oscillatory envelope argument.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- A genuine complex finite Volterra wave has a uniform energy-scaled bound under its original positive linear weighted kernel estimate.
Use: Support.naturalWave_exponential supplies the actual original support spectral wave, reference solution, kernel and growth weight. Bounded scaled energies then give precisely the uniform a priori bounds needed by the original edge limit and oscillatory envelope argument.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: divide the actual wave norms by the same genuine positive weight. The exact Volterra equation and weighted linear kernel bound give a triangular norm inequality on each original prefix. The proved finite-prefix Gronwall inequality bounds it by C*exp(B*norm(d)*(M+1)^2). -/
theorem weighted_volterra_bound (u v : ℕ→ℂ) (G : ℕ→ℕ→ℝ) (w : ℕ→ℝ)
    (d : ℂ) (M : ℕ) {C B : ℝ} (hC:0≤C) (hB:0≤B) (hw:∀j≤M,0<w j)
    (hu:∀j≤M,‖u j‖≤C*w j)
    (hG:∀j≤M,∀k<j,0≤G j k ∧ G j k*w k/w j≤B*((j-k:ℕ):ℝ))
    (hv:∀j≤M,v j=u j+d*∑k∈range j,(G j k:ℂ)*v k) :
    ‖v M‖≤C*w M*exp (B*‖d‖*((M:ℝ)+1)^2) := by
  -- Only the actual finite prefix is used; neither the Volterra equation nor the kernel bound is assumed on an unused tail.
  let f : ℕ→ℝ := fun j => ‖v j‖/w j
  let A : ℝ := ‖d‖*B*((M:ℝ)+1)
  have hA : 0≤A := by dsimp [A]; positivity
  have hcore := weighted_volterra_inequality u v G w d M hw hu hG hv
  have htri : ∀j≤M,f j≤C+A*∑k∈range j,f k := by
    intro j hj
    have hsum' : (∑k∈range j,((j-k:ℕ):ℝ)*f k)≤((M:ℝ)+1)*∑k∈range j,f k := by
      rw [mul_sum]
      apply sum_le_sum
      intro k hk
      have hkj := mem_range.mp hk
      have hfk : 0≤f k := div_nonneg (norm_nonneg _) (hw k (by omega)).le
      have hidx : ((j-k:ℕ):ℝ)≤(M:ℝ)+1 := by exact_mod_cast (show j-k≤M+1 by omega)
      exact mul_le_mul_of_nonneg_right hidx hfk
    calc
      f j≤C+(‖d‖*B)*∑k∈range j,((j-k:ℕ):ℝ)*f k := hcore j hj
      _ ≤ C+(‖d‖*B)*(((M:ℝ)+1)*∑k∈range j,f k) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum' (mul_nonneg (norm_nonneg d) hB))
      _ = _ := by dsimp [A]; ring
  have h := prefix_gronwall hC hA M htri
  have hdiv : ‖v M‖≤(C*exp (A*(M:ℝ)))*w M := (div_le_iff₀ (hw M le_rfl)).mp h
  have he : A*(M:ℝ)≤B*‖d‖*((M:ℝ)+1)^2 := by
    have hp : 0≤B*‖d‖*((M:ℝ)+1) := by positivity
    dsimp [A]
    nlinarith
  calc
    _ ≤ (C*exp (A*(M:ℝ)))*w M := hdiv
    _ = C*w M*exp (A*(M:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (mul_nonneg hC (hw M le_rfl).le)

end
end jacobi.Finite
