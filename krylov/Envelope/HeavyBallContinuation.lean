import krylov.Reference.HeavyBallCoefficients
import krylov.Reference.HeavyBallParameters
import krylov.Envelope.ContinuationCongruence
import krylov.Envelope.HeavyBallMaximum
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), actual heavy-ball CG continuation and exact maximum.
Use: derive the printed Chebyshev-U continuation and attained interval maximum from the genuine CG run on the actual finite heavy-ball matrix, with true square-root endpoint parameters.
Source: actual measured heavy-ball coefficients, genuine used-coefficient continuation congruence, real printed-parameter identities and the proved sharp Chebyshev endpoint bound.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference Polynomial Polynomial.Chebyshev chebyshev1
variable {N : ℕ}

/-- The genuine continuation of the actual heavy-ball CG run equals its true constant-coefficient continuation through every real finite suffix.
Use: The genuine continuation of the actual heavy-ball CG run equals its true constant-coefficient continuation through every real finite suffix.
Article: main_krylov, prop:phi(b), actual heavy-ball CG continuation and exact maximum.
Proof: Replace only actual used line lengths and genuine internal recurrence ratios; the true terminal beta is unused. -/
theorem heavyBall_phi_constant (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (j k : ℕ) (hjk : j+k≤N) :
    let Q := cgOperator (heavyBallMatrix d q N)
    let g := WithLp.toLp 2 (JacobiData.site N 0)
    phi (CG.length Q g) (CG.beta Q g) j k=phi (fun _ => d⁻¹) (fun _ => q^2) j k := by
  apply phi_coefficients_congr
  · intro i hi
    exact heavyBall_cg_length d q hd hq (j+i) (by omega)
  · intro i hi
    exact heavyBall_cg_beta_internal d q hd hq (j+i) (by omega)

/-- The actual finite heavy-ball CG continuation has the exact printed Chebyshev-U formula in the genuine original spectral coordinate.
Use: The actual finite heavy-ball CG continuation has the exact printed Chebyshev-U formula in the genuine original spectral coordinate.
Article: main_krylov, prop:phi(b), actual heavy-ball CG continuation and exact maximum.
Proof: Transfer the true measured coefficients and insert the actual square-root parameter coordinate identity. -/
theorem heavyBall_phi_printed (I : SpectralInterval) (j k : ℕ) (hjk : j+k≤N) (lam : ℝ) :
    let d := HeavyBallParameters.pivot I
    let q := HeavyBallParameters.ratio I
    let Q := cgOperator (heavyBallMatrix d q N)
    let g := WithLp.toLp 2 (JacobiData.site N 0)
    (phi (CG.length Q g) (CG.beta Q g) j k).eval lam=
      q^k*((U ℝ (k:ℤ)).eval (I.z lam)-q*(U ℝ ((k:ℤ)-1)).eval (I.z lam)) := by
  dsimp only
  rw [heavyBall_phi_constant _ _ (HeavyBallParameters.pivot_pos I) (HeavyBallParameters.ratio_domain I).1 j k hjk,
    constant_phi_chebyshev _ _ (inv_ne_zero (HeavyBallParameters.pivot_pos I).ne')
      (HeavyBallParameters.ratio_domain I).1.ne' j k lam,HeavyBallParameters.coordinate]

/-- The actual finite heavy-ball CG continuation attains exactly the printed largest absolute value on the original closed spectral interval.
Use: The actual finite heavy-ball CG continuation attains exactly the printed largest absolute value on the original closed spectral interval.
Article: main_krylov, prop:phi(b), actual heavy-ball CG continuation and exact maximum.
Proof: The genuine interval Chebyshev bound holds at every original point and the actual right endpoint attains the printed constant. -/
theorem heavyBall_phi_printed_maximum (I : SpectralInterval) (j k : ℕ) (hjk : j+k≤N) :
    let d := HeavyBallParameters.pivot I
    let q := HeavyBallParameters.ratio I
    let Q := cgOperator (heavyBallMatrix d q N)
    let g := WithLp.toLp 2 (JacobiData.site N 0)
    IsGreatest ((fun lam => |(phi (CG.length Q g) (CG.beta Q g) j k).eval lam|) '' Set.Icc I.mu I.L)
      (q^k*((k:ℝ)+1+q*k)) := by
  -- The actual endpoint coordinate and genuine CG coefficient transfer identify both the uniform bound and its real attainer.
  dsimp only
  let d := HeavyBallParameters.pivot I
  let q := HeavyBallParameters.ratio I
  have hd : d≠0 := (HeavyBallParameters.pivot_pos I).ne'
  have hq : 0 < q := (HeavyBallParameters.ratio_domain I).1
  have hzL : (1+q^2-d⁻¹*I.L)/(2*q)= -1 := by
    rw [HeavyBallParameters.coordinate]
    unfold SpectralInterval.z SpectralInterval.delta
    field_simp [(sub_pos.mpr I.mu_lt_L).ne']
    ring
  -- Keep the actual original interval point and genuine right-endpoint witness in the attained-maximum statement.
  rw [heavyBall_phi_constant d q (HeavyBallParameters.pivot_pos I) hq j k hjk]
  refine ⟨?_,?_⟩
  · exact ⟨I.L,⟨I.mu_lt_L.le,le_rfl⟩,constant_phi_abs_at_right d⁻¹ q (inv_ne_zero hd) hq j k I.L hzL⟩
  · rintro v ⟨lam,hlam,rfl⟩
    exact constant_phi_abs_bound d⁻¹ q (inv_ne_zero hd) hq j k lam (by
      rw [HeavyBallParameters.coordinate]
      exact abs_le.mpr (I.z_mem hlam))
end
end krylov.Envelope
