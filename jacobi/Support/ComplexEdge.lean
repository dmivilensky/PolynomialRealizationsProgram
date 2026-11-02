import jacobi.Support.NormalizedEdge
import jacobi.Support.TopHalfUniform

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The actual complex finite support polynomials have their genuine
uniform half-chain limit, with the exact printed Gamma amplitude.
The proof restores the original top solution after the normalized
Volterra limit; it includes the endpoint and arbitrary complex energy.
Use: the actual target/support Gram summands have their fixed-edge limits with the same original polynomials, rather than an assumed finite-edge certificate. The resulting Gram–Cholesky limit supplies the persymmetric eigenvectors in Theorems A–B and Theorem 2.1.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual degree-scaled complex support wave converges uniformly on its entire physical half chain to the reference solution with its original exact top amplitude.
Use: the actual target/support Gram summands have their fixed-edge limits with the same original polynomials, rather than an assumed finite-edge certificate. The resulting Gram–Cholesky limit supplies the persymmetric eigenvectors in Theorems A–B and Theorem 2.1.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: multiply the proved uniform normalized-wave convergence by the same actual degree-scaled positive top-node solution. That top solution converges uniformly to the actual U profile; compact continuity bounds both U and the genuine reference core. The exact product-error identity combines the two uniform errors, including zero. -/
theorem naturalWave_edge {a b:ℝ} (ha:-1<a) (hb:-1<b) (z:ℂ) (y:ℕ→ℂ)
    (hy:Tendsto (fun n => groundScaledEnergy a b n (y n)) atTop
      (𝓝 (((eigenvalue a 0:ℂ)-z)/2))) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,2*m≤n+1→
      ‖(((n:ℝ)^(-gamma a):ℝ):ℂ)*naturalWave a b ha hb n m (y n)-
        (topProfile a b ((m:ℝ)/(n:ℝ)):ℂ)*regularWave a z ((m:ℝ)/(n:ℝ))‖<ε := by
  -- Uniform bounds are taken for the actual continuum functions on the original closed half interval.
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s:=Icc (0:ℝ) (3/4)) (topProfile_continuous (b:=b) ha).continuousOn
  have hcore : ContinuousOn (regularWave a z) (Icc (0:ℝ) (3/4)) := by
    intro t ht
    exact (regularWave_analytic a z ⟨ht.1,by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s:=Icc (0:ℝ) (3/4)) hcore
  let M : ℝ := max C 0+1
  let Q : ℝ := max D 0+1
  have hM : 0<M := by dsimp [M]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  intro ε hε
  let η : ℝ := ε/(2*(M+Q+1))
  have hη : 0<η := div_pos hε (by positivity)
  obtain ⟨N,hv⟩ := naturalWave_normalized_edge ha hb z y hy η hη
  obtain ⟨L,hu⟩ := topValue_uniform_half ha hb η hη
  obtain ⟨P,hunit⟩ := topValue_uniform_half ha hb 1 (by norm_num)
  refine ⟨max (max N L) (max P 2),?_⟩
  intro n hn m hm
  have hnN : N≤n := (le_max_left N L).trans ((le_max_left (max N L) (max P 2)).trans hn)
  have hnL : L≤n := (le_max_right N L).trans ((le_max_left (max N L) (max P 2)).trans hn)
  have hnP : P≤n := (le_max_left P 2).trans ((le_max_right (max N L) (max P 2)).trans hn)
  have hnlarge : 2≤n := (le_max_right P 2).trans ((le_max_right (max N L) (max P 2)).trans hn)
  have hnpos : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hnpos
  let t : ℝ := (m:ℝ)/(n:ℝ)
  have ht : t∈Icc (0:ℝ) (3/4) := by
    refine ⟨by dsimp [t]; positivity,?_⟩
    apply (div_le_iff₀ hnR).mpr
    have hmn : 2*(m:ℝ)≤(n:ℝ)+1 := by exact_mod_cast hm
    have hn2 : (2:ℝ)≤n := by exact_mod_cast hnlarge
    linarith
  let T : ℂ := (((n:ℝ)^(-gamma a)*topValue a b ha hb n m:ℝ):ℂ)
  let U : ℂ := (topProfile a b t:ℂ)
  let q : ℂ := regularWave a z t
  have hTU : ‖T-U‖<η := by
    simpa only [T,U,t,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hu n hnL m hm
  have hTUone : ‖T-U‖<1 := by
    simpa only [T,U,t,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hunit n hnP m hm
  have hUnorm : ‖U‖≤max C 0 := by
    have h : ‖U‖≤C := by simpa only [U,Complex.norm_real,Real.norm_eq_abs] using hC t ht
    exact h.trans (le_max_left _ _)
  have hTnorm : ‖T‖≤M := by
    have h := norm_add_le (T-U) U
    rw [sub_add_cancel] at h
    exact h.trans (by dsimp [M]; linarith)
  have hqnorm : ‖q‖≤Q := (hD t ht).trans (by dsimp [Q]; linarith [le_max_left D 0])
  have hun : (topValue a b ha hb n m:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (naturalPolynomial_top_pos ha hb (by omega)).ne'
  have heq : (((n:ℝ)^(-gamma a):ℝ):ℂ)*naturalWave a b ha hb n m (y n)-U*q=
      T*(naturalWave a b ha hb n m (y n)/(topValue a b ha hb n m:ℂ)-q)+(T-U)*q := by
    dsimp only [T]
    push_cast
    field_simp [hun]
    ring
  change ‖(((n:ℝ)^(-gamma a):ℝ):ℂ)*naturalWave a b ha hb n m (y n)-U*q‖<ε
  rw [heq]
  calc
    _ ≤ ‖T‖*‖naturalWave a b ha hb n m (y n)/(topValue a b ha hb n m:ℂ)-q‖+‖T-U‖*‖q‖ := by
      simpa only [norm_mul] using norm_add_le
        (T*(naturalWave a b ha hb n m (y n)/(topValue a b ha hb n m:ℂ)-q)) ((T-U)*q)
    _ ≤ M*η+η*Q := add_le_add
      (mul_le_mul hTnorm (hv n hnN m hm).le (norm_nonneg _) hM.le)
      (mul_le_mul hTU.le hqnorm (norm_nonneg _) hη.le)
    _ ≤ (M+Q+1)*η := by nlinarith [hη.le]
    _ = ε/2 := by dsimp [η]; field_simp
    _ < ε := by linarith

end
end jacobi.Support
