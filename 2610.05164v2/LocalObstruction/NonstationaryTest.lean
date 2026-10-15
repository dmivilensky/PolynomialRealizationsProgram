import «2610.05164v2».LocalObstruction.TestFunctions
import «2610.05164v2».LocalObstruction.SineContradiction

/-!
Article: 2610.05164v2, Theorem 6.1.
The variational contradiction in H: any continuous observation gradient with a constant plus
exponential tail fails to annihilate the two-constraint tangent space at the actual sine density.
Use: `«2610.05164v2».LocalObstruction.sine_nonstationary_test` feeds
`«2610.05164v2».LocalObstruction.no_local_lower_bound_of_gradient_with_property` (no local lower
bound of gradient with property).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Real Set Filter MeasureTheory Asymptotics «2610.05164v2».SineContinuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

 /--
Constructs witnesses with the exact properties `∃ v : SmoothTest, (∫ x, v x)=0 ∧ (∫ x, v x/(2*n
x))=0 ∧ (∫ x, v x*((3/2:ℝ)*n x-g x))≠0`.

Use: `«2610.05164v2».LocalObstruction.no_local_lower_bound_of_gradient` uses this identity to
establish constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f
x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧ (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f
x))=1 ∧ (∀ x, |f x-m x|<ε) ∧ densityEnergy f<B f`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities. Prove equality of functions by evaluating both sides at an
arbitrary argument.
-/
theorem sine_nonstationary_test {g : ℝ → ℝ} (hg : Continuous g) {c₀ c₁ : ℝ}
    (htail : (fun x => g x-c₀-c₁*exp (-2*x)) =o[atTop] n) :
    ∃ v : SmoothTest, (∫ x, v x)=0 ∧ (∫ x, v x/(2*n x))=0 ∧
      (∫ x, v x*((3/2:ℝ)*n x-g x))≠0 := by
  -- Establish continuity hweight before using the function at limits or in calculus arguments.
  have hweight : Continuous (fun x => 1/(2*n x)) :=
    continuous_const.div (continuous_const.mul n_continuous)
      (fun x => (mul_pos (by norm_num) (n_positive x)).ne')
  let m₀ := testIntegral (fun _ => 1) continuous_const
  let m₁ := testIntegral (fun x => 1/(2*n x)) hweight
  let L := testIntegral (fun x => (3/2:ℝ)*n x-g x)
    ((continuous_const.mul n_continuous).sub hg)
  by_contra h
  have hker : ∀ v : SmoothTest, m₀ v=0 → m₁ v=0 → L v=0 := by
    intro v hv₀ hv₁
    by_contra hv
    apply h
    refine ⟨v,?_,?_,hv⟩
    · simpa [m₀,testIntegral] using hv₀
    · simpa [m₁,testIntegral,div_eq_mul_inv] using hv₁
  obtain ⟨w₀,w₁,h₀,h₁,hind⟩ := sine_normalization_directions
  have h0 : m₀ w₀=1 := by simpa [m₀,testIntegral] using h₀
  have h1 : m₀ w₁=1 := by simpa [m₀,testIntegral] using h₁
  have hd : m₁ w₀≠m₁ w₁ := by simpa [m₁,testIntegral,div_eq_mul_inv] using hind
  obtain ⟨α,ζ,hα⟩ := two_constraint_annihilator m₀ m₁ L h0 h1 hd hker
  have hzero : (fun x => (3/2:ℝ)*n x-g x-α-ζ/(2*n x))=0 := by
    apply continuous_eq_zero_of_test_integrals
      ((((continuous_const.mul n_continuous).sub hg).sub continuous_const).sub
        (continuous_const.div (continuous_const.mul n_continuous)
          (fun x => (mul_pos (by norm_num) (n_positive x)).ne')))
    intro v hv hc
    let V : SmoothTest := ⟨v,hv,hc⟩
    have hi := hα V
    have hie : (∫ x, V x*((3/2:ℝ)*n x-g x))=
        α*(∫ x, V x)+ζ*(∫ x, V x/(2*n x)) := by
      simpa [L,m₀,m₁,testIntegral,div_eq_mul_inv] using hi
    change (∫ x, V x*((3/2:ℝ)*n x-g x-α-ζ/(2*n x)))=0
    have hexp : (fun x => V x*((3/2:ℝ)*n x-g x-α-ζ/(2*n x)))=
        fun x => V x*((3/2:ℝ)*n x-g x)-V x*α-V x*(ζ/(2*n x)) := by
      funext x
      ring
    rw [hexp]
    have hA := test_integrable V (g := fun x => (3/2:ℝ)*n x-g x)
      ((continuous_const.mul n_continuous).sub hg)
    have hB := test_integrable V (g := fun _ => α) continuous_const
    have hC := test_integrable V (g := fun x => ζ/(2*n x))
      (continuous_const.div (continuous_const.mul n_continuous)
        (fun x => (mul_pos (by norm_num) (n_positive x)).ne'))
    have hi₁ := integral_sub (hA.sub hB) hC
    have hi₂ := integral_sub hA hB
    simp only [Pi.sub_apply] at hi₁ hi₂
    rw [hi₁,hi₂]
    have he : (fun x => V x*(ζ/(2*n x)))=fun x => ζ*(V x/(2*n x)) := by
      funext x
      ring
    rw [he,integral_const_mul,integral_mul_const]
    linarith [hie]
  apply no_sine_stationary_identity (α := α) (ζ := ζ) htail
  exact Eventually.of_forall (fun x => by
    have hi := congrFun hzero x
    change (3/2:ℝ)*n x-g x-α-ζ/(2*n x)=0 at hi
    linarith)

end
end «2610.05164v2».LocalObstruction
