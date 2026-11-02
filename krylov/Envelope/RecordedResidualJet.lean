import krylov.Envelope.ActualCorrectionJets

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(a), genuine last recorded-step residual cancellation.
Use: transfer actual final current-direction residual cancellation to
the true combined recorded-step residual under the source smooth class,
including every genuine original and appended correction movement.
Source: primitive-derived actual correction jets, true CG Krylov
orthogonality and genuine scalar/vector product derivative rules.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For every actual smooth source method, zero genuine final current-direction residual derivative implies zero true final combined recorded-step residual derivative.
Use: For every actual smooth source method, zero genuine final current-direction residual derivative implies zero true final combined recorded-step residual derivative.
Article: main_krylov, apB:lem:mu(a), genuine last recorded-step residual cancellation.
Proof: The real total correction is zero at the genuine quadratic reference and its actual derivative lies in the true next Krylov flag, orthogonal to the real final CG gradient. Actual exact-search scalar regularity transfers the zero genuine direction residual derivative to the real line step; adding the actual correction movement gives the true recorded-step result. -/
theorem recorded_residual_deriv_zero_of_direction (M : SmoothProbedClass E)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (hA : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<k+1, CG.gradient Q g i≠0)
    (hline : deriv (fun t => inner ℝ (probedDirection M.policy (A t) (B t) g k)
      (probedGradient M.policy (A t) (B t) g (k+1))) 0=0) :
    deriv (fun t => inner ℝ (probedStep M.policy (A t) (B t) g k)
      (probedGradient M.policy (A t) (B t) g (k+1))) 0=0 := by
  -- Derive the genuine scalar, direction, final-gradient and correction-movement regularity from the actual primitive smooth source class.
  let m := M.policy
  let F := fun t => probedGradient m (A t) (B t) g (k+1)
  let d := fun t => probedDirection m (A t) (B t) g k
  let χ := fun t => (probedPhase m (A t) (B t) g k).movement
  let α := fun t => lineLength (probedGradient m (A t) (B t) g k) (d t) (probedProbe m (A t) (B t) g k)
  have hs := M.smooth Q hQ hpos g (k+1) hpre
  have hfields := smoothProbed_fields_regular m M.consistent A B (fun _ => g) 0 (k+1) hA hB contDiffAt_const
    Q hA0 hB0 hQ hpos hpre hs k (by omega)
  have hF : ContDiffAt ℝ 2 F 0 := smoothProbed_gradient_regular m M.consistent A B (fun _ => g) 0 (k+1)
    hA hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hs
  have hα : ContDiffAt ℝ 2 α 0 := (smoothProbed_search_regular m M.consistent A B (fun _ => g) 0 (k+1)
    hA hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hs k (by omega)).1
  have hF0 : F 0=CG.gradient Q g (k+1) := by
    dsimp only [F]
    rw [hA0,hB0]
    exact quadratic_gradient_eq_cg m M.consistent Q hQ hpos g (k+1)
  have hχ0 : χ 0=0 := by
    dsimp only [χ,probedPhase]
    rw [hA0,hB0]
    exact (zeroCorrections_change_operator _ Q Q _ (M.consistent Q hQ hpos g k).choose_spec.2.2).2.1
  -- The true zero-reference total correction jet lies in the actual next Krylov flag, orthogonal to the genuine final CG gradient.
  have hχK : deriv χ 0∈CG.krylovSpace Q g (k+1) :=
    (actual_correction_jets M.memory m M.consistent M.admissible A B (fun _ => g) (k+1) hA hB contDiffAt_const
      Q hA0 hB0 hQ hpos hpre hs k (by omega)).1
  have hχG : inner ℝ (deriv χ 0) (F 0)=0 := by
    rw [hF0]
    exact CG.gradient_orthogonal_krylov Q hQ hpos g (k+1) hpre hχK
  have hχpair : HasDerivAt (fun t => inner ℝ (χ t) (F t)) 0 0 := by
    have hh := ((hfields.2.2.2).differentiableAt (by norm_num)).hasDerivAt.inner ℝ
      (hF.differentiableAt (by norm_num)).hasDerivAt
    change HasDerivAt (fun t => inner ℝ (χ t) (F t))
      (inner ℝ (χ 0) (deriv F 0)+inner ℝ (deriv χ 0) (F 0)) 0 at hh
    simpa only [hχ0,inner_zero_left,zero_add,hχG] using hh
  -- Apply real scalar product differentiation to the actual line step, then add the genuine zero correction-pairing derivative.
  have hdF : ContDiffAt ℝ 2 (fun t => inner ℝ (d t) (F t)) 0 := hfields.1.inner ℝ hF
  have hdF0 : inner ℝ (d 0) (F 0)=0 := by
    obtain ⟨c,_,hd,_⟩ := M.consistent Q hQ hpos g k
    dsimp only [d,probedDirection]
    rw [hA0,hB0,hF0,hd,real_inner_smul_left,(CG.invariant Q hQ hpos g (k+1) hpre).old_direction k (by omega),mul_zero]
  have hlineLocal : deriv (fun t => inner ℝ (d t) (F t)) 0=0 := hline
  have hαpair : HasDerivAt (fun t => α t*inner ℝ (d t) (F t)) 0 0 := by
    have hh := (hα.differentiableAt (by norm_num)).hasDerivAt.mul (hdF.differentiableAt (by norm_num)).hasDerivAt
    convert! hh using 1
    simp only [hdF0,hlineLocal,mul_zero,zero_add]
  have hf := hαpair.add hχpair
  have heq : (fun t => inner ℝ (probedStep m (A t) (B t) g k) (F t))=
      ((fun t => α t*inner ℝ (d t) (F t))+(fun t => inner ℝ (χ t) (F t))) := by
    funext t
    simp only [Pi.add_apply,probedStep,probedDirection,probedProbe,inner_add_left,real_inner_smul_left,F,d,χ,α,probedGradient]
  change deriv (fun t => inner ℝ (probedStep m (A t) (B t) g k) (F t)) 0=0
  rw [heq]
  simpa only [zero_add] using hf.deriv
end
end krylov.Envelope
