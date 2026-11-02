import krylov.LinearAlgebra.ProjectionAugmentation
import krylov.Convergence.WindowAugmentation

/-!
Article: main_krylov, thm:Ip, stored and augmented RFC distances.
Use: bound the actual orthogonal projection of the new probe using only
the genuine stored synthesis gain and measured small pairings.
Source: the normal equations for the true orthogonal projection and
Cauchy--Schwarz for finite coefficients. No projection bound is assumed.
-/
namespace krylov.LinearAlgebra
noncomputable section
open krylov.Methods krylov.Convergence
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {p : ℕ}

/-- A genuine synthesis lower gain and small probe pairings control the
actual projection onto the stored span, with the precise square-root
dimension factor. Article: main_krylov, thm:Ip. -/
theorem starProjection_of_gain (s : Fin p → E) (d : E) {sigma epsilon : ℝ}
    (hsigma : 0<sigma) (hepsilon : 0≤epsilon)
    (hgain : ∀ c : Fin p → ℝ,sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2)
    (hpair : ∀ i,|inner ℝ (s i) d|≤epsilon) :
    ‖(Submodule.span ℝ (Set.range s)).starProjection d‖≤Real.sqrt p*epsilon/sigma := by
  let V := Submodule.span ℝ (Set.range s)
  let v := V.starProjection d
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (V.starProjection_apply_mem d)
  have hcv : combine s c=v := hc
  have hg := hgain c
  rw [hcv] at hg
  have hcn : sigma*‖WithLp.toLp 2 c‖≤‖v‖ := by
    nlinarith only [hg,norm_nonneg v,norm_nonneg (WithLp.toLp 2 c),hsigma,
      sq_nonneg (sigma*‖WithLp.toLp 2 c‖-‖v‖)]
  have hp := combine_pairing_bound s d hepsilon hpair c
  rw [hcv] at hp
  have ho := V.starProjection_inner_eq_zero d v (V.starProjection_apply_mem d)
  have hid : inner ℝ v d=‖v‖^2 := by
    change inner ℝ (d-v) v=0 at ho
    rw [inner_sub_left,real_inner_self_eq_norm_sq] at ho
    rw [real_inner_comm]
    exact sub_eq_zero.mp ho
  rw [hid,abs_of_nonneg (sq_nonneg _)] at hp
  change ‖v‖≤Real.sqrt p*epsilon/sigma
  apply (le_div_iff₀ hsigma).mpr
  by_cases hv : ‖v‖=0
  · simpa only [hv,zero_mul] using mul_nonneg (Real.sqrt_nonneg (p:ℝ)) hepsilon
  · have hmul := mul_le_mul_of_nonneg_left hcn (mul_nonneg (Real.sqrt_nonneg (p:ℝ)) hepsilon)
    have hscale := mul_le_mul_of_nonneg_left hp hsigma.le
    have hvpos := (norm_nonneg v).lt_of_ne' hv
    nlinarith only [hmul,hscale,hvpos]

end
end krylov.LinearAlgebra
