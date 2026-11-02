import krylov.Reference.HeavyBallMeasure
import krylov.Envelope.HeavyBallContinuation
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), complete original heavy-ball measure continuation.
Use: derive the printed polynomial and exact attained maximum for every genuine original reference whose normalized gradient spectral measure equals the constructed actual positive-edge heavy-ball measure.
Source: actual spectral-measure coefficient invariance, true finite continuation coefficient dependence and the genuine measured heavy-ball endpoint maximum.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference Polynomial Polynomial.Chebyshev chebyshev1
variable {n N : ℕ}

/-- Every true original reference with the genuine heavy-ball spectral measure has exactly the actual constant heavy-ball continuation on every real used suffix.
Use: Every true original reference with the genuine heavy-ball spectral measure has exactly the actual constant heavy-ball continuation on every real used suffix.
Article: main_krylov, prop:phi(b), complete original heavy-ball measure continuation.
Proof: Use the genuine measured coefficient theorem only at actual used line and internal recurrence indices. -/
theorem heavyBall_measure_phi_constant (I : SpectralInterval) (hN : 0 < N)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0)
    (hmeasure : ∀ f,gradientSpectralIntegral base hb g hg f=heavyBallSpectralIntegral I N hN f)
    (j k : ℕ) (hjk : j+k≤N) :
    phi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) j k=
      phi (fun _ => (HeavyBallParameters.pivot I)⁻¹) (fun _ => (HeavyBallParameters.ratio I)^2) j k := by
  apply phi_coefficients_congr
  · intro i hi
    exact (heavyBall_measure_coefficients I hN base hb g hg hmeasure (j+i) (by omega)).1
  · intro i hi
    exact (heavyBall_measure_coefficients I hN base hb g hg hmeasure (j+i) (by omega)).2.1 (by omega)

/-- Every genuine original reference with the actual heavy-ball spectral measure has the exact printed Chebyshev-U continuation formula.
Use: Every genuine original reference with the actual heavy-ball spectral measure has the exact printed Chebyshev-U continuation formula.
Article: main_krylov, prop:phi(b), complete original heavy-ball measure continuation.
Proof: Transfer the actual spectral-measure coefficients and insert the true original spectral-coordinate identity. -/
theorem heavyBall_measure_phi_formula (I : SpectralInterval) (hN : 0 < N)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0)
    (hmeasure : ∀ f,gradientSpectralIntegral base hb g hg f=heavyBallSpectralIntegral I N hN f)
    (j k : ℕ) (hjk : j+k≤N) (lam : ℝ) :
    let q := HeavyBallParameters.ratio I
    (phi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) j k).eval lam=
      q^k*((U ℝ (k:ℤ)).eval (I.z lam)-q*(U ℝ ((k:ℤ)-1)).eval (I.z lam)) := by
  dsimp only
  rw [heavyBall_measure_phi_constant I hN base hb g hg hmeasure j k hjk,
    constant_phi_chebyshev _ _ (inv_ne_zero (HeavyBallParameters.pivot_pos I).ne')
      (HeavyBallParameters.ratio_domain I).1.ne' j k lam,HeavyBallParameters.coordinate]

/-- Every genuine original reference with the actual heavy-ball spectral measure has the exact attained printed continuation maximum on the original interval.
Use: Every genuine original reference with the actual heavy-ball spectral measure has the exact attained printed continuation maximum on the original interval.
Article: main_krylov, prop:phi(b), complete original heavy-ball measure continuation.
Proof: Identify its genuine polynomial with the actual heavy-ball executor polynomial before using its real interval bound and right-endpoint attainer. -/
theorem heavyBall_measure_phi_maximum (I : SpectralInterval) (hN : 0 < N)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0)
    (hmeasure : ∀ f,gradientSpectralIntegral base hb g hg f=heavyBallSpectralIntegral I N hN f)
    (j k : ℕ) (hjk : j+k≤N) :
    let q := HeavyBallParameters.ratio I
    IsGreatest ((fun lam => |(phi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) j k).eval lam|)
      '' Set.Icc I.mu I.L) (q^k*((k:ℝ)+1+q*k)) := by
  -- Genuine measure equality identifies the actual polynomial itself, so the true interval maximum and its original endpoint attainer transfer together.
  dsimp only
  have he : phi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) j k=
      phi (CG.length (cgOperator (heavyBallMatrix (HeavyBallParameters.pivot I) (HeavyBallParameters.ratio I) N))
        (heavyBallInitial N)) (CG.beta (cgOperator
        (heavyBallMatrix (HeavyBallParameters.pivot I) (HeavyBallParameters.ratio I) N)) (heavyBallInitial N)) j k := by
    dsimp only [heavyBallInitial]
    rw [heavyBall_measure_phi_constant I hN base hb g hg hmeasure j k hjk,
      heavyBall_phi_constant _ _ (HeavyBallParameters.pivot_pos I) (HeavyBallParameters.ratio_domain I).1 j k hjk]
  rw [he]
  exact heavyBall_phi_printed_maximum I j k hjk
end
end krylov.Envelope
