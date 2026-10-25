import polyak.Levels.Program.Grid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Article: lem:pinid, including negative lags, all residue classes and
the derivative identity for a differentiable phase. -/

noncomputable section
namespace polyak.Levels

theorem pinning_identity (Θ : Curve) (k : ℕ) (r m : ℤ) (ω : Frequency) :
    Θ.lag (r+m*k) ω=Real.cos (Θ ω)-
      Real.cos ((m:ℝ)*k*(ω:ℝ)-(Θ ω-(r:ℝ)*(ω:ℝ))) := by
  unfold Curve.lag
  push_cast
  congr 2
  ring

theorem cos_lag_add_mul_grid {k : ℕ} {ω : Frequency}
    (hω : ω∈periodicGrid k) (r m : ℤ) (θ : ℝ) :
    Real.cos (((r+m*k:ℤ):ℝ)*(ω:ℝ)-θ)=Real.cos ((r:ℝ)*(ω:ℝ)-θ) := by
  rcases hω.2 with ⟨j,hj⟩
  have he : ((r+m*k:ℤ):ℝ)*(ω:ℝ)-θ=
      ((r:ℝ)*(ω:ℝ)-θ)+((m*j:ℤ):ℝ)*(2*Real.pi) := by
    push_cast
    linear_combination (m:ℝ)*hj
  rw [he,Real.cos_add_int_mul_two_pi]

theorem sin_lag_add_mul_grid {k : ℕ} {ω : Frequency}
    (hω : ω∈periodicGrid k) (r m : ℤ) (θ : ℝ) :
    Real.sin (((r+m*k:ℤ):ℝ)*(ω:ℝ)-θ)=Real.sin ((r:ℝ)*(ω:ℝ)-θ) := by
  rcases hω.2 with ⟨j,hj⟩
  have he : ((r+m*k:ℤ):ℝ)*(ω:ℝ)-θ=
      ((r:ℝ)*(ω:ℝ)-θ)+((m*j:ℤ):ℝ)*(2*Real.pi) := by
    push_cast
    linear_combination (m:ℝ)*hj
  rw [he,Real.sin_add_int_mul_two_pi]

theorem lag_add_mul_grid (Θ : Curve) {k : ℕ} {ω : Frequency}
    (hω : ω∈periodicGrid k) (r m : ℤ) : Θ.lag (r+m*k) ω=Θ.lag r ω := by
  unfold Curve.lag
  rw [cos_lag_add_mul_grid hω]

theorem lag_mod_grid (Θ : Curve) {k : ℕ} {ω : Frequency}
    (hω : ω∈periodicGrid k) (n : ℤ) : Θ.lag n ω=Θ.lag (n%k) ω := by
  have he : n=n%k+(n/k)*k:=(Int.emod_add_ediv_mul n k).symm
  conv_lhs => rw [he]
  exact lag_add_mul_grid Θ hω (n%k) (n/k)

theorem hasDerivAt_lag_phase {θ : ℝ→ℝ} {θ' ω : ℝ}
    (hθ : HasDerivAt θ θ' ω) (n : ℤ) :
    HasDerivAt (fun x : ℝ=>Real.cos (θ x)-Real.cos ((n:ℝ)*x-θ x))
      (-θ'*Real.sin (θ ω)+((n:ℝ)-θ')*Real.sin ((n:ℝ)*ω-θ ω)) ω := by
  have hlin : HasDerivAt (fun x : ℝ=>(n:ℝ)*x-θ x) ((n:ℝ)-θ') ω := by
    convert ((hasDerivAt_id ω).const_mul (n:ℝ)).sub hθ using 1 <;> first | rfl | simp only [mul_one]
  convert hθ.cos.sub hlin.cos using 1
  ring

theorem pinning_derivative {θ : ℝ→ℝ} {θ' : ℝ} {k : ℕ} {ω : Frequency}
    (hθ : HasDerivAt θ θ' (ω:ℝ)) (hω : ω∈periodicGrid k) (r m : ℤ) :
    deriv (fun x : ℝ=>Real.cos (θ x)-Real.cos (((r+m*k:ℤ):ℝ)*x-θ x)) (ω:ℝ)=
      deriv (fun x : ℝ=>Real.cos (θ x)-Real.cos ((r:ℝ)*x-θ x)) (ω:ℝ)+
        (m:ℝ)*k*Real.sin ((r:ℝ)*(ω:ℝ)-θ ω) := by
  rw [(hasDerivAt_lag_phase hθ _).deriv,(hasDerivAt_lag_phase hθ _).deriv,
    sin_lag_add_mul_grid hω]
  push_cast
  ring

end polyak.Levels
