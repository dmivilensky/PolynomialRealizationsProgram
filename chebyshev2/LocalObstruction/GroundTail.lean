import chebyshev2.LocalObstruction.SineConvolutionTail
import chebyshev2.GroundState.Article
import chebyshev2.GroundState.Convolution

/-!
Article: chebyshev2, Theorem 6.1.
Lemma 26(iv): the squared actual sine ground state has an exponential leading term and an o(n)
remainder.
Use: `chebyshev2.LocalObstruction.sine_ground_square_tail` feeds
`chebyshev2.LocalObstruction.theorem_6_1` (theorem 6 1).
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory Asymptotics chebyshev2.SineContinuum
open chebyshev2.GroundState chebyshev2.Sobolev chebyshev2.Continuum
open scoped Topology InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Integrability of the displayed function: `Integrable (fun y => exp y*m y)`.

Use: `chebyshev2.LocalObstruction.sine_dominated_first_moment` uses this integrability
result to establish integrability of the displayed function: `Integrable (fun y => exp y*j y)`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.m_integrable`,
`chebyshev2.LocalObstruction.sine_weighted_moment_integrable`,
`chebyshev2.SineContinuum.m_continuous` with the arguments shown in the proof.
-/
theorem sine_first_moment_integrable : Integrable (fun y => exp y*m y) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.m_integrable`,
  -- `chebyshev2.LocalObstruction.sine_weighted_moment_integrable`,
  -- `chebyshev2.SineContinuum.m_continuous` with the arguments shown in the proof.
  apply (m_integrable.add sine_weighted_moment_integrable).mono'
    (continuous_exp.mul m_continuous).aestronglyMeasurable
  apply Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply,Pi.add_apply]
  rw [norm_of_nonneg (mul_nonneg (exp_pos _).le (m_positive y).le)]
  have he : exp y≤1+exp (2*y) := by
    rw [show 2*y=y+y by ring,exp_add]
    nlinarith [sq_nonneg (exp y-1)]
  nlinarith [mul_le_mul_of_nonneg_right he (m_positive y).le]

/--
Integrability of the displayed function: `Integrable (fun y => exp y*j y)`.

Use: `chebyshev2.LocalObstruction.sine_dominated_convolution_bound` uses this integrability
result to prove the bound `|H1.rep (convolution j) x-(∫ y, exp y*j
y)*exp (-x)|≤K*weightedSineTail x`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.sine_ground_square_tail`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sine_dominated_first_moment {j : ℝ → ℝ} (hj : Integrable j)
    {K : ℝ} (_hK : 0≤K) (hb : ∀ y, |j y|≤K*m y) :
    Integrable (fun y => exp y*j y) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (sine_first_moment_integrable.const_mul K).mono'
    (continuous_exp.aestronglyMeasurable.mul hj.aestronglyMeasurable)
  filter_upwards with y
  dsimp only [Pi.mul_apply]
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (exp_pos _),Real.norm_eq_abs]
  calc
    _ ≤ exp y*(K*m y) := mul_le_mul_of_nonneg_left (hb y) (exp_pos _).le
    _ = _ := by ring

/--
The stated quantitative bound `|H1.rep (convolution j) x-(∫ y, exp y*j y)*exp
(-x)|≤K*weightedSineTail x`.

Use: `chebyshev2.LocalObstruction.sine_dominated_convolution_tail` uses this bound to
establish the stated quantitative bound `(fun x => H1.rep (convolution j) x-(∫ y, exp y*j
y)*exp (-x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.sine_ground_square_tail`.

Proof: Separate `y ∈ Ioi x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem sine_dominated_convolution_bound {j : ℝ → ℝ} (hj : Integrable j)
    {K : ℝ} (hK : 0≤K) (hb : ∀ y, |j y|≤K*m y) {x : ℝ} (hx : 1≤x) :
    |H1.rep (convolution j) x-(∫ y, exp y*j y)*exp (-x)|≤K*weightedSineTail x := by
  -- Separate `y ∈ Ioi x` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  let f := fun y => (exp (-|x-y|)-exp (-x)*exp y)*j y
  have hi := sine_dominated_first_moment hj hK hb
  have he : H1.rep (convolution j) x-(∫ y, exp y*j y)*exp (-x)=∫ y, f y := by
    rw [convolution_rep hj]
    have hex : (fun y => exp (-|x-y|)*j y-exp (-x)*(exp y*j y))=f := by funext y; dsimp [f]; ring
    rw [← mul_comm (exp (-x)),← integral_const_mul,← integral_sub
      (convolution_kernel_integrable hj x) (hi.const_mul _),hex]
  -- Establish hdom as the integrability justification for the later integral estimates or
  -- changes of order.
  have hdom : Integrable ((Ioi x).indicator (fun y => K*(exp (2*(y-x))*m y))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr ((weightedSineTail_integrable hx).const_mul K)
  have hbound : ∀ y, ‖f y‖≤(Ioi x).indicator (fun y => K*(exp (2*(y-x))*m y)) y := by
    intro y
    have hex : exp (-x)*exp y=exp (y-x) := by rw [← exp_add]; congr 1; ring
    by_cases hy : y ∈ Ioi x
    · have hxy : x<y := hy
      rw [indicator_of_mem hy]
      have hab : exp (-|x-y|)≤exp (y-x) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy.le)]
        apply exp_le_exp.mpr
        linarith
      have hle : exp (y-x)≤exp (2*(y-x)) := exp_le_exp.mpr (by linarith)
      dsimp only [f]
      rw [norm_mul,Real.norm_eq_abs,hex,abs_of_nonpos (sub_nonpos.mpr hab),Real.norm_eq_abs]
      calc
        _ ≤ exp (y-x)*(K*m y) := mul_le_mul (by linarith [exp_pos (-|x-y|)]) (hb y)
          (abs_nonneg _) (exp_pos _).le
        _ ≤ exp (2*(y-x))*(K*m y) := mul_le_mul_of_nonneg_right hle (mul_nonneg hK (m_positive y).le)
        _ = _ := by ring
    · have hxy : y≤x := le_of_not_gt hy
      rw [indicator_of_notMem hy]
      dsimp only [f]
      rw [hex,abs_of_nonneg (sub_nonneg.mpr hxy),show -(x-y)=y-x by ring,sub_self,zero_mul,norm_zero]
  rw [he]
  have h := norm_integral_le_of_norm_le hdom (Eventually.of_forall hbound)
  rw [integral_indicator measurableSet_Ioi,integral_const_mul] at h
  exact h

/--
The stated quantitative bound `(fun x => H1.rep (convolution j) x-(∫ y, exp y*j y)*exp (-x))
=o[atTop] n`.

Use: `chebyshev2.LocalObstruction.sine_ground_square_tail` uses this identity to establish
constructs witnesses with the exact properties `∃ C : ℝ, (fun x => (H1.rep G.u x)^2-C*exp
(-2*x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.sine_ground_square_tail`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem sine_dominated_convolution_tail {j : ℝ → ℝ} (hj : Integrable j)
    {K : ℝ} (hK : 0≤K) (hb : ∀ y, |j y|≤K*m y) :
    (fun x => H1.rep (convolution j) x-(∫ y, exp y*j y)*exp (-x)) =o[atTop] n := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [weightedSineTail_littleO.bound (div_pos hc (by linarith : 0<K+1)),
    eventually_ge_atTop (1:ℝ)] with x ht hx
  rw [Real.norm_eq_abs,abs_of_nonneg (weightedSineTail_bounds hx).1] at ht
  rw [Real.norm_eq_abs]
  calc
    _ ≤ K*weightedSineTail x := sine_dominated_convolution_bound hj hK hb hx
    _ ≤ (K+1)*weightedSineTail x := mul_le_mul_of_nonneg_right (by linarith) (weightedSineTail_bounds hx).1
    _ ≤ (K+1)*(c/(K+1)*‖n x‖) := mul_le_mul_of_nonneg_left ht (by linarith)
    _ = _ := by field_simp

 /--
Exact identity `H1.rep G.u x=H1.rep (convolution (fun y => groundParameter hf hn/2*f y*H1.rep
G.u y)) x`.

Use: `chebyshev2.LocalObstruction.sine_ground_square_tail` rewrites with this identity to
establish constructs witnesses with the exact properties `∃ C : ℝ, (fun x => (H1.rep G.u
x)^2-C*exp (-2*x)) =o[atTop] n`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.sine_ground_square_tail`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity. Prove equality of functions by evaluating both sides at an
arbitrary argument.
-/
theorem ground_source_rep {f : ℝ → ℝ} {hf : Integrable f} {hn : ∀ x, 0≤f x}
    (G : GroundWitness hf hn) (x : ℝ) :
    H1.rep G.u x=H1.rep (convolution (fun y =>
      groundParameter hf hn/2*f y*H1.rep G.u y)) x := by
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun y => f y*H1.rep G.u y) :=
    hf.mul_bdd (H1.continuous_rep G.u).aestronglyMeasurable
      (Eventually.of_forall (fun y => H1.evaluation_bound G.u y))
  have he := congrArg (fun z : H1 => H1.rep z x) G.eigen
  rw [H1.rep_smul] at he
  have hrep : H1.rep (densityOperator f G.u) x=
      ∫ y, exp (-|x-y|)*(f y*H1.rep G.u y) := by
    unfold H1.rep causalValue
    rw [densityOperator_inner hf,← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      dsimp only
      rw [feature_inner,abs_sub_comm x y]
      ring)
  rw [hrep] at he
  rw [convolution_rep (by convert! hi.const_mul (groundParameter hf hn/2) using 1; funext y; ring)]
  have hs : groundParameter hf hn/2*kernelEigenvalue hf hn 0=1 := by
    unfold groundParameter
    field_simp [(top_density_attained hf hn G.mass_positive).1.ne']
  calc
    _ = groundParameter hf hn/2*(kernelEigenvalue hf hn 0*H1.rep G.u x) := by rw [← mul_assoc,hs,one_mul]
    _ = groundParameter hf hn/2*(∫ y, exp (-|x-y|)*(f y*H1.rep G.u y)) := by rw [he]
    _ = _ := by rw [← integral_const_mul]; congr 1; funext y; ring

 /--
Constructs witnesses with the exact properties `∃ C : ℝ, (fun x => (H1.rep G.u x)^2-C*exp
(-2*x)) =o[atTop] n`.

Use: `chebyshev2.LocalObstruction.groundSquareGradient` uses this identity in the displayed
construction of `groundSquareGradient`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sine_ground_square_tail
    (G : GroundWitness m_integrable (fun x => (m_positive x).le)) :
    ∃ C : ℝ, (fun x => (H1.rep G.u x)^2-C*exp (-2*x)) =o[atTop] n := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let κ := groundParameter m_integrable (fun x => (m_positive x).le)
  let j := fun y => κ/2*m y*H1.rep G.u y
  let K := κ/2*(‖G.u‖/sqrt 2)
  have hκ : 0<κ := G.coupling_positive
  have hK : 0≤K := mul_nonneg (div_nonneg hκ.le (by norm_num))
    (div_nonneg (norm_nonneg _) (sqrt_nonneg _))
  -- Establish hj as the integrability justification for the later integral estimates or
  -- changes of order.
  have hj : Integrable j := by
    have hi := m_integrable.mul_bdd (H1.continuous_rep G.u).aestronglyMeasurable
      (Eventually.of_forall (fun y => H1.evaluation_bound G.u y))
    convert! hi.const_mul (κ/2) using 1
    funext y
    ring
  have hb : ∀ y, |j y|≤K*m y := by
    intro y
    dsimp only [j,K]
    rw [abs_mul,abs_mul,abs_of_nonneg (div_nonneg hκ.le (by norm_num)),
      abs_of_nonneg (m_positive y).le]
    calc
      _ ≤ κ/2*m y*(‖G.u‖/sqrt 2) := mul_le_mul_of_nonneg_left (H1.evaluation_bound G.u y)
        (mul_nonneg (div_nonneg hκ.le (by norm_num)) (m_positive y).le)
      _ = _ := by ring
  let c := ∫ y, exp y*j y
  have hrem : (fun x => H1.rep (convolution j) x-c*exp (-x)) =o[atTop] n :=
    sine_dominated_convolution_tail hj hK hb
  -- Record the convergence hex with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hex : Tendsto (fun x : ℝ => exp (-x)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hbig : (fun x => H1.rep (convolution j) x+c*exp (-x)) =O[atTop] (fun _ => (1:ℝ)) :=
    ((H1.rep_tendsto_zero (convolution j)).1.add (hex.const_mul c)).isBigO_one ℝ
  have hmul := hrem.mul_isBigO hbig
  refine ⟨c^2,?_⟩
  have he : (fun x => (H1.rep G.u x)^2-c^2*exp (-2*x))=
      fun x => (H1.rep (convolution j) x-c*exp (-x))*(H1.rep (convolution j) x+c*exp (-x)) := by
    funext x
    rw [ground_source_rep G x]
    change (H1.rep (convolution j) x)^2-c^2*exp (-2*x)=_
    rw [show -2*x=-x+(-x) by ring,exp_add]
    ring
  rw [he]
  simpa only [mul_one] using hmul

end
end chebyshev2.LocalObstruction
