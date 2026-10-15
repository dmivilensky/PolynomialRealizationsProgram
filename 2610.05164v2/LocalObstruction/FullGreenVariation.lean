import «2610.05164v2».LocalObstruction.FullGreen
import «2610.05164v2».LocalObstruction.OperatorPerturbation

/-!
Article: 2610.05164v2, Lemma 26.
Signed density variations of the actual full resolvent and its kernel.
Result: `«2610.05164v2».LocalObstruction.resolventGreen_density_derivative` supplies the stated
article conclusion.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open MeasureTheory «2610.05164v2».Continuum
open scoped InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => fullResolvent (m+ε • v) s)
(-((fullResolvent m s) ∘L ((s/2) • densityOperator v) ∘L (fullResolvent m s))) 0`.

Use: `«2610.05164v2».LocalObstruction.resolventGreen_density_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
resolventGreen (m+ε • v) s x y) (-s*(∫ z,resolventGreen m s x z*resolventGreen m s z y*v z))
0`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.resolventGreen_density_derivative`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem fullResolvent_density_derivative {m v : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x,0≤m x) (hv : Integrable v) {s : ℝ} (hs : 0≤s) :
    HasDerivAt (fun ε : ℝ => fullResolvent (m+ε • v) s)
      (-((fullResolvent m s) ∘L ((s/2) • densityOperator v) ∘L (fullResolvent m s))) 0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun ε : ℝ => fullPencil (m+ε • v) s)=
      fun ε : ℝ => fullPencil m s+ε • ((s/2) • densityOperator v) := by
    funext ε
    dsimp only [fullPencil]
    rw [densityOperator_add hm (hv.smul ε),densityOperator_smul]
    module
  have hp : HasDerivAt (fun ε : ℝ => fullPencil (m+ε • v) s)
      ((s/2) • densityOperator v) 0 := by
    rw [he]
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const ((s/2) • densityOperator v)).const_add (fullPencil m s)
  let hu := fullPencil_unit hm hn hs
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [IsUnit.unit_spec] at hi
  have hpoint : fullPencil (m+(0:ℝ) • v) s=fullPencil m s := by simp
  have hi' := hi
  conv at hi' => arg 3; rw [← hpoint]
  convert! hi'.comp_hasDerivAt 0 hp using 1
  simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    fullResolvent,Ring.inverse_of_isUnit hu]
  rfl

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => resolventGreen (m+ε • v) s
x y) (-s*(∫ z,resolventGreen m s x z*resolventGreen m s z y*v z)) 0`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 26.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem resolventGreen_density_derivative {m v : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x,0≤m x) (hv : Integrable v) {s : ℝ} (hs : 0≤s) (x y : ℝ) :
    HasDerivAt (fun ε : ℝ => resolventGreen (m+ε • v) s x y)
      (-s*(∫ z,resolventGreen m s x z*resolventGreen m s z y*v z)) 0 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hR := (fullResolvent_density_derivative hm hn hv hs).clm_apply (hasDerivAt_const 0 (feature y))
  have hd := ((hasDerivAt_const 0 (feature x)).inner ℝ hR).div_const 2
  have he : inner ℝ (feature x)
      ((-((fullResolvent m s) ∘L ((s/2) • densityOperator v) ∘L (fullResolvent m s)))
        (feature y))/2=
      -s*(∫ z,resolventGreen m s x z*resolventGreen m s z y*v z) := by
    simp only [neg_apply,ContinuousLinearMap.comp_apply,smul_apply,
      map_smul,inner_neg_right,real_inner_smul_right]
    rw [← fullResolvent_symmetric hm hn hs,densityOperator_inner hv]
    rw [← integral_const_mul,neg_div]
    rw [neg_mul,← integral_const_mul]
    congr 1
    rw [← integral_div]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only
      unfold resolventGreen
      rw [← fullResolvent_symmetric hm hn hs (feature x) (feature z),
        real_inner_comm (fullResolvent m s (feature x)) (feature z)]
      ring)
  convert! hd using 1
  simpa only [map_zero,zero_add,add_zero,inner_zero_left] using he.symm

end
end «2610.05164v2».LocalObstruction
