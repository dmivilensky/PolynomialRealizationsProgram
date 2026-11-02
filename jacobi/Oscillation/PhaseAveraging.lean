import jacobi.Oscillation.PerturbedVariation

/-!
Article: jacobi, Proposition B.1.
The already proved integrated invariant estimate is converted back into
the true difference of the two ordinary phases. All oscillatory endpoint
terms are bounded by the true phase difference, so the result retains
its uniform inverse-square frequency error on the entire growing interval.
Use: recovers the actual finite Jacobi phase correction from the integrated modified-invariant estimate.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The true invariant difference differs from the genuine averaged phase difference only by controlled oscillatory endpoint terms.
Use: recovers the actual finite Jacobi phase correction from the integrated modified-invariant estimate.
Article: jacobi, Proposition B.1.
Proof: cancel the two common nonoscillatory Bessel terms. The double-angle
coordinates are two-Lipschitz, so the two differences are bounded by
|c| *|f-g|/(2*x^2) and |c| *|f-g|/(2*x^3); compare x^3 with x^2 and bound
the remaining finite sine correction by |e|/4. -/
theorem invariant_phase_recovery (c : ℝ) (f g e P : ℝ → ℝ) {x : ℝ} (hx : 1≤x) :
    |(perturbedInvariant c f e P x-phaseInvariant c g x)-(f x-g x-P x/2)|≤
      |c| *|f x-g x|/x^2+|e x|/4 := by
  -- The constant and inverse-linear corrections cancel exactly because both original phases use the same inverse-square coefficient.
  have hxp : 0<x := by linarith
  let u := (c/(4*x^2))*(sin (2*f x)-sin (2*g x))
  let v := (c/(4*x^3))*(cos (2*f x)-cos (2*g x))
  let w := (e x/4)*sin (2*f x)
  have he : (perturbedInvariant c f e P x-phaseInvariant c g x)-(f x-g x-P x/2)=u-v+w := by
    dsimp [perturbedInvariant,phaseInvariant,u,v,w]
    ring
  have hd := double_angle_lipschitz (f x) (g x)
  have hu : |u|≤ |c|/(4*x^2)*(2*|f x-g x|) := by
    dsimp [u]
    rw [abs_mul,abs_div,abs_of_pos (by positivity : 0<4*x^2)]
    exact mul_le_mul_of_nonneg_left hd.2 (by positivity)
  have hv : |v|≤ |c|/(4*x^2)*(2*|f x-g x|) := by
    dsimp [v]
    rw [abs_mul,abs_div,abs_of_pos (by positivity : 0<4*x^3)]
    have hh : |c|/(4*x^3)≤ |c|/(4*x^2) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      (by nlinarith [mul_le_mul_of_nonneg_left hx (show 0≤x^2 by positivity)])
    exact (mul_le_mul_of_nonneg_left hd.1 (by positivity)).trans (mul_le_mul_of_nonneg_right hh (by positivity))
  have hw : |w|≤ |e x|/4 := by
    dsimp [w]
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)).trans_eq (mul_one _)
  rw [he]
  calc
    _ ≤ |u|+|v|+|w| := (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ |c|/(4*x^2)*(2*|f x-g x|)+|c|/(4*x^2)*(2*|f x-g x|)+|e x|/4 := add_le_add (add_le_add hu hv) hw
    _ = _ := by ring

/-- Actual linear phase control bounds the genuine oscillatory recovery error uniformly, independently of the terminal phase index.
Use: converts the true integrated invariant estimate into the printed uniform averaged-phase error.
Article: jacobi, Proposition B.1.
Proof: substitute the actual linear phase bound into the recovery estimate,
then use 1/x<=1 and |e|<=epsilon for x>=1. -/
theorem invariant_recovery_uniform (c : ℝ) (f g e P : ℝ → ℝ) {x epsilon B : ℝ}
    (hx : 1≤x) (heps : 0≤epsilon) (hB : 0≤B)
    (hphase : |f x-g x|≤B*epsilon*x) (he : |e x|≤epsilon) :
    |(perturbedInvariant c f e P x-phaseInvariant c g x)-(f x-g x-P x/2)|≤
      (|c| *B+1)*epsilon := by
  -- The actual phase difference cancels one denominator power; the remaining inverse factor is at most one.
  have hxp : 0<x := by linarith
  have hfirst : |c| *|f x-g x|/x^2≤ |c| *B*epsilon := by
    calc
      _ ≤ |c| *(B*epsilon*x)/x^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hphase (abs_nonneg _)) (by positivity)
      _ = |c| *B*epsilon/x := by field_simp [hxp.ne']
      _ ≤ _ := div_le_self (by positivity) hx
  have h := invariant_phase_recovery c f g e P hx
  have hh : |e x|/4≤epsilon := by linarith
  calc
    _ ≤ |c| *B*epsilon+epsilon := h.trans (add_le_add hfirst hh)
    _ = _ := by ring

/-- The actual perturbed phase equals the true Bessel phase plus half the actual perturbation primitive, with a uniform error of order epsilon on the full growing interval.
Use: the original scaled Jacobi phase instantiates this theorem to prove the exact regular-potential correction in Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: combine the genuine linear barrier, the uniform integrated invariant
estimate and the proved recovery bounds at both original endpoints. The
initial discrepancy and initial primitive are genuinely small by their
stated initial data; no averaged phase or zero estimate is a premise. -/
theorem phase_averaging {f g e e' P : ℝ → ℝ} {c epsilon B a y N L : ℝ}
    (ha : 1≤a) (hlarge : 4*|c|≤a) (hay : a≤y) (hN : 0<N) (hy : y≤L*N)
    (heps : 0<epsilon) (hepsN : epsilon≤1/N) (hB : 2<B)
    (hf : ∀ x∈Icc a y,HasDerivAt f (1+(c/x^2+e x)*sin (f x)^2) x)
    (hg : ∀ x∈Icc a y,HasDerivAt g (1+c/x^2*sin (g x)^2) x)
    (he : ∀ x∈Icc a y,HasDerivAt e (e' x) x)
    (hP : ∀ x∈Icc a y,HasDerivAt P (e x) x)
    (hebound : ∀ x∈Icc a y,|e x|≤epsilon)
    (he'bound : ∀ x∈Icc a y,|e' x|≤epsilon/N)
    (hinit : |f a-g a|≤B*epsilon*a) (hPinit : |P a|≤epsilon*a) :
    |f y-g y-P y/2|≤
      (B*a+a/2+2*(|c| *B+1)+((4*c^2+2*|c|)*B+2*|c|+1)*(1+L))*epsilon := by
  -- Every comparison concerns the actual phases and their literal primitive; recover both endpoint values before estimating their integrated difference.
  let F := fun x => perturbedInvariant c f e P x-phaseInvariant c g x
  have ha0 : 0<a := by linarith
  have hB0 : 0≤B := by linarith
  have hp := phase_linear_perturbation ha0 hlarge heps hB hf hg hebound hinit
  have hyrec := invariant_recovery_uniform c f g e P (ha.trans hay) heps.le hB0
    (hp y ⟨hay,le_rfl⟩) (hebound y ⟨hay,le_rfl⟩)
  have harec := invariant_recovery_uniform c f g e P ha heps.le hB0 hinit (hebound a ⟨le_rfl,hay⟩)
  have hvar := perturbedInvariant_variation ha hlarge hay hN hy heps hepsN hB hf hg he hP hebound he'bound hinit
  have hPa : |P a/2|≤epsilon*a/2 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right hPinit (by norm_num)
  have hFa : |F a|≤B*epsilon*a+epsilon*a/2+(|c| *B+1)*epsilon := by
    have h1 := abs_sub (f a-g a) (P a/2)
    have h2 := abs_sub (F a) (f a-g a-P a/2)
    have h3 := abs_add_le (F a-(f a-g a-P a/2)) (f a-g a-P a/2)
    rw [sub_add_cancel] at h3
    dsimp [F] at h1 h2 h3 ⊢
    linarith
  have hsum := abs_add_le (F y-F a) (F a)
  rw [sub_add_cancel] at hsum
  have hlast := abs_sub (F y) (F y-(f y-g y-P y/2))
  rw [sub_sub_cancel] at hlast
  have heq : (B*a+a/2+2*(|c| *B+1)+((4*c^2+2*|c|)*B+2*|c|+1)*(1+L))*epsilon=
      B*epsilon*a+epsilon*a/2+2*((|c| *B+1)*epsilon)+
        (((4*c^2+2*|c|)*B+2*|c|+1)*epsilon)*(1+L) := by ring
  rw [heq]
  dsimp [F] at hsum hlast
  linarith

end
end jacobi.Oscillation
