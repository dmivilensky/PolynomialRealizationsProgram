import polyak.Levels.Program.Pinning
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Pinning derivatives within a domain, including one-sided endpoint
interpretations on the closed frequency interval. -/
noncomputable section
namespace polyak.Levels

theorem hasDerivWithinAt_lag_phase {θ : ℝ→ℝ} {θ' ω : ℝ} {S : Set ℝ}
    (hθ : HasDerivWithinAt θ θ' S ω) (n : ℤ) :
    HasDerivWithinAt (fun x : ℝ=>Real.cos (θ x)-Real.cos ((n:ℝ)*x-θ x))
      (-θ'*Real.sin (θ ω)+((n:ℝ)-θ')*Real.sin ((n:ℝ)*ω-θ ω)) S ω := by
  have hlin : HasDerivWithinAt (fun x : ℝ=>(n:ℝ)*x-θ x) ((n:ℝ)-θ') S ω := by
    convert ((hasDerivWithinAt_id ω S).const_mul (n:ℝ)).sub hθ using 1 <;>
      first | rfl | simp only [mul_one]
  convert hθ.cos.sub hlin.cos using 1
  ring

theorem pinning_derivativeWithin {θ : ℝ→ℝ} {θ' : ℝ} {k : ℕ} {ω : Frequency}
    {S : Set ℝ} (hunique : UniqueDiffWithinAt ℝ S (ω:ℝ))
    (hθ : HasDerivWithinAt θ θ' S (ω:ℝ)) (hω : ω∈periodicGrid k) (r m : ℤ) :
    derivWithin (fun x : ℝ=>Real.cos (θ x)-Real.cos (((r+m*k:ℤ):ℝ)*x-θ x)) S (ω:ℝ)=
      derivWithin (fun x : ℝ=>Real.cos (θ x)-Real.cos ((r:ℝ)*x-θ x)) S (ω:ℝ)+
        (m:ℝ)*k*Real.sin ((r:ℝ)*(ω:ℝ)-θ ω) := by
  rw [(hasDerivWithinAt_lag_phase hθ _).derivWithin hunique,
    (hasDerivWithinAt_lag_phase hθ _).derivWithin hunique,sin_lag_add_mul_grid hω]
  push_cast
  ring

theorem pinning_derivative_closedInterval {θ : ℝ→ℝ} {θ' : ℝ} {k : ℕ} {ω : Frequency}
    (hθ : HasDerivWithinAt θ θ' (Set.Icc 0 Real.pi) (ω:ℝ))
    (hω : ω∈periodicGrid k) (r m : ℤ) :
    derivWithin (fun x : ℝ=>Real.cos (θ x)-Real.cos (((r+m*k:ℤ):ℝ)*x-θ x)) (Set.Icc 0 Real.pi) (ω:ℝ)=
      derivWithin (fun x : ℝ=>Real.cos (θ x)-Real.cos ((r:ℝ)*x-θ x)) (Set.Icc 0 Real.pi) (ω:ℝ)+
        (m:ℝ)*k*Real.sin ((r:ℝ)*(ω:ℝ)-θ ω) := by
  apply pinning_derivativeWithin ?_ hθ hω
  exact (uniqueDiffOn_Icc Real.pi_pos) ω ω.property

end polyak.Levels
