import jacobi.Support.EdgeResidual
import jacobi.Finite.NestedVolterraStability

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The actual ground-normalized finite orthogonal polynomials converge
uniformly on the complete physical half chain at every convergent
complex scaled energy. The finite equation, continuum approximation
and stability are all proved for the original objects.
Use: naturalWave_edge restores the actual top-node normalization and proves the full original complex finite-polynomial edge limit needed by the two-edge Gram limit, Cholesky asymptotics and persymmetric eigenvectors.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter Finset jacobi.Reference
open scoped Topology

/-- The actual normalized complex support wave converges uniformly to the genuine reference core for every convergent complex scaled spectral energy.
Use: naturalWave_edge restores the actual top-node normalization and proves the full original complex finite-polynomial edge limit needed by the two-edge Gram limit, Cholesky asymptotics and persymmetric eigenvectors.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: subtract the actual reference core from the exact original normalized finite equation. Its forcing is exactly the previously proved uniformly vanishing actual residual. The actual normalized kernel has a uniform bound and the actual scaled energies are bounded. Finite nested Volterra stability therefore gives a uniform Gronwall factor at arbitrary complex energy, without an assumed finite-limit certificate. -/
theorem naturalWave_normalized_edge {a b:ℝ} (ha:-1<a) (hb:-1<b) (z:ℂ) (y:ℕ→ℂ)
    (hy:Tendsto (fun n => groundScaledEnergy a b n (y n)) atTop
      (𝓝 (((eigenvalue a 0:ℂ)-z)/2))) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,2*m≤n+1→
      ‖naturalWave a b ha hb n m (y n)/(topValue a b ha hb n m:ℂ)-
        regularWave a z ((m:ℝ)/(n:ℝ))‖<ε := by
  -- The original reference displacement need not be small; only its proved degree-scaled bound is used.
  obtain ⟨B,hB,hbound⟩ := normalizedKernel_bound ha hb
  let A : ℝ := ‖((eigenvalue a 0:ℂ)-z)/2‖+1
  have hA : 0<A := by dsimp [A]; positivity
  have henergy : ∀ᶠn:ℕ in atTop,‖groundScaledEnergy a b n (y n)‖≤A :=
    (hy.norm.eventually (Iio_mem_nhds (by dsimp [A]; linarith))).mono (fun _ h => h.le)
  intro ε hε
  let η : ℝ := ε/(2*exp (A*B))
  have hη : 0<η := div_pos hε (by positivity)
  obtain ⟨N,hres⟩ := edgeResidual_uniform ha hb z y hy η hη
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hbound.and henergy)
  refine ⟨max (max N L) 1,?_⟩
  intro n hn m hm
  have hnN : N≤n := (le_max_left N L).trans ((le_max_left (max N L) 1).trans hn)
  have hnL : L≤n := (le_max_right N L).trans ((le_max_left (max N L) 1).trans hn)
  have hnpos : 0<n := lt_of_lt_of_le (by norm_num : 0<1) ((le_max_right (max N L) 1).trans hn)
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast hnpos.ne'
  obtain ⟨hK,hE⟩ := hL n hnL
  let d : ℂ := y n-(cos (gamma a*step a b (n+1)):ℝ)
  let v (j:ℕ) := naturalWave a b ha hb n j (y n)/(topValue a b ha hb n j:ℂ)
  let q (j:ℕ) := regularWave a z ((j:ℝ)/(n:ℝ))
  let e (j:ℕ) := v j-q j
  have hnormK (l:ℕ) (hl:l<m) (j:ℕ) (hj:j≤l) :
      ‖(normalizedKernel a b ha hb n l j:ℂ)‖≤B := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hK l j (by omega) hj).1]
    exact (hK l j (by omega) hj).2
  have hr (r:ℕ) (hr:r≤m) :
      ‖e r-d*∑l∈range r,∑j∈range (l+1),(normalizedKernel a b ha hb n l j:ℂ)*e j‖≤η := by
    have heq : e r-d*∑l∈range r,∑j∈range (l+1),(normalizedKernel a b ha hb n l j:ℂ)*e j=
        -edgeResidual a b ha hb z (y n) n r := by
      have hs : (∑l∈range r,∑j∈range (l+1),(normalizedKernel a b ha hb n l j:ℂ)*e j)=
          (∑l∈range r,∑j∈range (l+1),(normalizedKernel a b ha hb n l j:ℂ)*v j)-
          (∑l∈range r,∑j∈range (l+1),(normalizedKernel a b ha hb n l j:ℂ)*q j) := by
        simp only [e,mul_sub,sum_sub_distrib]
      rw [hs]
      dsimp only [e,v,q,d]
      rw [naturalWave_normalizedVolterra a b ha hb n r (by omega) (y n)]
      dsimp only [edgeResidual,groundScaledEnergy,finiteGroundMesh]
      field_simp [hn0]
      ring
    rw [heq,norm_neg]
    exact (hres n hnN r (by omega)).le
  have hstab := jacobi.Finite.nested_volterra_stability e
    (fun l j => (normalizedKernel a b ha hb n l j:ℂ)) d m hB.le hη.le hnormK hr
  have hexp : ‖d‖*B*(m:ℝ)^2≤A*B := by
    have hmn : (m:ℝ)≤n := by exact_mod_cast (show m≤n by omega)
    calc
      _ = B*((m:ℝ)^2*‖d‖) := by ring
      _ ≤ B*((n:ℝ)^2*‖d‖) := by gcongr
      _ = B*‖groundScaledEnergy a b n (y n)‖ := by
        rw [groundScaledEnergy,norm_mul,norm_pow,Complex.norm_natCast]
      _ ≤ B*A := mul_le_mul_of_nonneg_left hE hB.le
      _ = _ := mul_comm _ _
  calc
    _ ≤ η*exp (‖d‖*B*(m:ℝ)^2) := hstab
    _ ≤ η*exp (A*B) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) hη.le
    _ = ε/2 := by dsimp [η]; field_simp
    _ < ε := by linarith

end
end jacobi.Support
