import chebyshev2.LocalObstruction.GreenPairing

/-!
Article: chebyshev2, Theorem 6.1.
Scale differentiation of the actual density gradient of H.
Use: `chebyshev2.LocalObstruction.green_density_gradient_scale_derivative` feeds
`chebyshev2.LocalObstruction.singleHPrime_density_derivative` (single HPrime density
derivative).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Filters
open scoped Topology InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Integrability of the displayed function: `Integrable (fun x => greenKernel s m x x*v x)`.

Use: `chebyshev2.LocalObstruction.green_density_gradient_scale_derivative` uses this
integrability result to establish the actual derivative at the stated point: `HasDerivAt (fun t
: ℝ => t*(∫ x,greenKernel t m x x*v x)) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v
x) s`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem green_diagonal_pair_integrable {m v : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (hc : Continuous m) {s : ℝ} (hs : 0≤s) (he : ∀ x,m (-x)=m x) (hv : Integrable v) :
    Integrable (fun x => greenKernel s m x x*v x) := by
  convert! (feature_diagonal_integrable hv (fullResolvent m s)).div_const 2 using 1
  funext x
  rw [greenKernel_eq_resolventGreen hm hn hc hs he]
  unfold resolventGreen
  ring

 /--
Integrability of the displayed function: `Integrable (fun x => greenScaleGradient s m x*v x)`.

Use: `chebyshev2.LocalObstruction.green_density_gradient_scale_derivative` uses this
integrability result to establish the actual derivative at the stated point: `HasDerivAt (fun t
: ℝ => t*(∫ x,greenKernel t m x x*v x)) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v
x) s`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem green_scale_pair_integrable {m v : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (hc : Continuous m) {s : ℝ} (hs : 0≤s) (he : ∀ x,m (-x)=m x) (hv : Integrable v) :
    Integrable (fun x => greenScaleGradient s m x*v x) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let A := -((fullResolvent m s) ∘L ((1/2:ℝ) • densityOperator m) ∘L (fullResolvent m s))
  convert! (feature_diagonal_integrable hv A).div_const 2 using 1
  funext x
  rw [greenScaleGradient_operator hm hn hc hs he]
  dsimp only [A]
  simp only [neg_apply,ContinuousLinearMap.comp_apply,smul_apply,map_smul,
    inner_neg_right,real_inner_smul_right]
  rw [← fullResolvent_symmetric hm hn hs]
  ring

 /--
The actual derivative at the stated point: `HasDerivAt (fun t : ℝ => t*(∫ x,greenKernel t m x
x*v x)) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) s`.

Use: `chebyshev2.LocalObstruction.singleHPrime_density_derivative` rewrites with this
derivative formula to establish the actual derivative at the stated point: `HasDerivAt
(singleHPrime hm hv s) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem green_density_gradient_scale_derivative {m v : ℝ → ℝ}
    (hm : Integrable m) (hn : ∀ x,0≤m x) (hc : Continuous m) {s : ℝ} (hs : 0<s)
    (he : ∀ x,m (-x)=m x) (hv : Integrable v) :
    HasDerivAt (fun t : ℝ => t*(∫ x,greenKernel t m x x*v x))
      (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) s := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hD := (featureDiagonal hv).hasFDerivAt.comp_hasDerivAt s
    (fullResolvent_derivative hm hn hs.le)
  have hd := ((hasDerivAt_id s).div_const 2).mul hD
  dsimp only [Function.comp_def,Pi.mul_apply,id_eq] at hd
  have hcoeff : (1/2:ℝ)*featureDiagonal hv (fullResolvent m s)+
      s/2*featureDiagonal hv (-((fullResolvent m s) ∘L ((1/2:ℝ) • densityOperator m) ∘L
        (fullResolvent m s)))=
      ∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x := by
    have hi := integral_add (green_diagonal_pair_integrable hm hn hc hs.le he hv)
      ((green_scale_pair_integrable hm hn hc hs.le he hv).const_mul s)
    have hf : (fun x => (greenKernel s m x x+s*greenScaleGradient s m x)*v x)=
        fun x => greenKernel s m x x*v x+s*(greenScaleGradient s m x*v x) := by funext x;ring
    rw [hf,hi,integral_const_mul,
      green_integral_operator hm hn hc hs.le he hv,
      green_gradient_integral_operator hm hn hc hs.le he hv]
    ring
  rw [hcoeff] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  rw [green_integral_operator hm hn hc ht.le he hv]
  dsimp only [Pi.mul_apply]
  ring

end
end chebyshev2.LocalObstruction
