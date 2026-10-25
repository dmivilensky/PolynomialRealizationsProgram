import chebyshev1.SineJacobi.EllipticRationalIntegral
import chebyshev1.Analysis.IntegralSquareBound

/-!
Article: chebyshev1, Theorem 5.2.
Cauchy--Schwarz and the elementary rational integral give a uniform bound for K².
Use: `chebyshev1.SineJacobi.ellipticK_square_bound` feeds
`chebyshev1.SineJacobi.sineProfile_square_bound` (sine Profile square bound).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi` — chebyshev1, Theorem 5.2;
Exact sine gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set MeasureTheory

/--
Cauchy--Schwarz and the elementary rational integral give a uniform bound for K².

The stated quantitative bound `ellipticK k^2 ≤ Real.pi^2/(4*sqrt (1-k^2))`.

Use: `chebyshev1.SineJacobi.sineProfile_square_bound` uses this bound to establish the
stated quantitative bound `sineProfile t^2 ≤ (2/Real.pi)*sin (Real.pi*t/2)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem ellipticK_square_bound {k : ℝ} (hk : |k| < 1) :
    ellipticK k^2 ≤ Real.pi^2/(4*sqrt (1-k^2)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hc := elliptic_integrand_continuous k hk
  have h1 := hc.intervalIntegrable (μ := volume) 0 (Real.pi/2)
  have h2 := (hc.pow 2).intervalIntegrable (μ := volume) 0 (Real.pi/2)
  have hh := chebyshev1.Analysis.integral_square_bound (half_pos pi_pos) h1 h2
  have he : (fun theta => (1/sqrt (1-k^2*sin theta^2))^2) =
      fun theta => 1/(1-k^2*sin theta^2) := by
    funext theta
    rw [div_pow, one_pow, sq_sqrt (elliptic_den_pos k theta hk).le]
  rw [he, ellipticRational_integral hk] at hh
  simp only [sub_zero] at hh
  change ellipticK k^2 ≤ (Real.pi/2)*(Real.pi/(2*sqrt (1-k^2))) at hh
  convert hh using 1 ; ring

end
end chebyshev1.SineJacobi
