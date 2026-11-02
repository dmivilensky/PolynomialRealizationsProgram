import krylov.OneGradient.KnownBaseTwoQueryLower
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), finite uniform minimax loss tending to one.
Use: pass from the genuine physical all-method lower bound to the
original second-order coefficient without regularity of competing methods.
Source: exact algebraic normalization of the finite four-adversary loss.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
open Filter Topology

/-- The explicit genuine finite four-model loss after cancelling the
positive perturbation scale. It is a polynomial in that scale.
Use: the same loss works for every original physical method and scenario.
Article: main_krylov, thm:local(c), uniform finite minimax loss. -/
def twoQueryMinimaxLoss (W w omega : ℝ) : ℝ :=
  1+(W+w)*omega+(W+w)*W/w*omega+
    twoDimensionalValue W w/w*omega*(1+(W+w)*omega)

/-- The actual finite lower-game coefficient is exactly the common
polynomial loss at every positive perturbation scale.
Use: no policy-dependent error term enters the asymptotic minimax limit.
Article: main_krylov, thm:local(c), exact finite loss normalization.
Proof: the true positive output radius and scale justify cancellation;
clear the two nonzero real denominators and collect equal monomials. -/
theorem twoQueryMinimaxLoss_eq (W w omega : ℝ) (hw : 0< w) :
    1+(W*omega+w*omega)+(W*omega+w*omega)*(W*omega)/(w*omega)+
      (twoDimensionalValue W w*omega^2)/(w*omega)*(1+W*omega+w*omega)=
      twoQueryMinimaxLoss W w omega := by
  unfold twoQueryMinimaxLoss
  field_simp [hw.ne']
  ring

/-- The genuine finite minimax loss tends to one along every shrinking
budget family, independently of all actual competing decisions.
Use: pathological or separately recalibrated policies are allowed.
Article: main_krylov, thm:local(c), uniform minimax limit loss.
Proof: the real loss is a fixed polynomial with constant term one. -/
theorem twoQueryMinimaxLoss_tendsto
    {ι : Type*} {l : Filter ι} (W w : ℝ) (scale : ι → ℝ)
    (hscale : Tendsto scale l (𝓝 0)) :
    Tendsto (fun j => twoQueryMinimaxLoss W w (scale j)) l (𝓝 1) := by
  have hc : ContinuousAt (twoQueryMinimaxLoss W w) 0 := by
    unfold twoQueryMinimaxLoss
    fun_prop
  simpa only [Function.comp_def,twoQueryMinimaxLoss,mul_zero,zero_mul,add_zero] using hc.tendsto.comp hscale

/-- Every actual physical second-order guarantee is at least V2 divided
by one explicit common polynomial loss, at each positive scale.
Use: the original source-class lower bound is already uniform before
choosing a limiting sequence or taking an infimum over methods.
Article: main_krylov, thm:local(c), finite normalized physical obstruction.
Proof: apply the actual all-method physical lower bound and cancel the
true positive scale squared; use its exact polynomial loss identity. -/
theorem knownBaseTwoQueryGuarantee_normalized_lower
    (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2)
    (W w omega v : ℝ) (hW : 0< W) (hw : 0< w) (homega : 0< omega)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin 2))) (hm : OneGradientSpanRestricted m)
    (hguarantee : knownBaseTwoQueryGuarantee base g (W*omega) (w*omega) m (v*omega^2)) :
    twoDimensionalValue W w≤ twoQueryMinimaxLoss W w omega*v := by
  have h := knownBaseTwoQueryGuarantee_finite_lower base hb g hc W w omega (v*omega^2) hW hw homega m hm hguarantee
  rw [twoQueryMinimaxLoss_eq W w omega hw] at h
  have he : twoQueryMinimaxLoss W w omega*(v*omega^2)=
      (twoQueryMinimaxLoss W w omega*v)*omega^2 := by ring
  rw [he] at h
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos homega)).mp h

end
end krylov.OneGradient
