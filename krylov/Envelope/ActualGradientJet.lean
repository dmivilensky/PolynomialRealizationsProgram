import krylov.Methods.SmoothProbedFields
import krylov.Envelope.FirstJets

/-!
Article: Lemma B.12 [apB:lem:filtration] of krylov.tex.
Use: prove the source true first-variation identity delta-g=A delta-x+J
for every genuinely executed smooth CG-consistent raw method, including all
finite correction observations and the actual physical iterate displacement.
Source: the exact real recorded-secant defect identity, proved actual primitive
field regularity, true quadratic step consistency, zero reference corrections
and standard operator/vector product differentiation followed by telescoping.
-/

namespace krylov.Envelope
noncomputable section
open Filter Topology krylov.Methods krylov.Reference
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


/-- The genuine physical iterate displacement of an actual raw history is exactly the chronological sum of its real recorded total steps.
Use: The genuine physical iterate displacement of an actual raw history is exactly the chronological sum of its real recorded total steps.
Article: main_krylov, apB:lem:filtration, actual raw-method gradient variation balance.
Proof: The actual executor prepends exactly one true physical step; finite sums agree by commutativity. -/
theorem history_displacement_eq_steps (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (N : ℕ) :
    (methodRun m A B g N).displacement=∑ i∈Finset.range N, probedStep m A B g i := by
  induction N with
  | zero => rfl
  | succ k ih =>
    change probedStep m A B g k+(methodRun m A B g k).displacement=_
    rw [ih,Finset.sum_range_succ]
    exact add_comm _ _

/-- The genuine first derivative of an executed smooth raw-method gradient is the actual reference operator applied to the sum of its true step derivatives plus the real reference-step injection sum.
Use: The genuine first derivative of an executed smooth raw-method gradient is the actual reference operator applied to the sum of its true step derivatives plus the real reference-step injection sum.
Article: main_krylov, apB:lem:filtration, actual raw-method gradient variation balance.
Proof: Primitive smooth-policy charts derive all actual gradient, step and correction-movement derivatives. Differentiate the exact real pair defect; actual reference corrections vanish and both reference segment operators equal the real quadratic. Genuine step consistency identifies every source injection, and finite telescoping yields the identity. -/
theorem probed_gradient_jet_sum (m : ProbedMethod E) (hm : CGConsistent m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q) (N : ℕ)
    (hA : ∀ k < N, ContDiffAt ℝ 2 (fun t => A t k) 0)
    (hB : ∀ k < N, ContDiffAt ℝ 2 (fun t => B t k) 0)
    (hpre : ∀ k < N, CG.gradient Q g k≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N) :
    deriv (fun t => probedGradient m (A t) (B t) g N) 0=
      Q (∑ k∈Finset.range N, deriv (fun t => probedStep m (A t) (B t) g k) 0)+
        ∑ k∈Finset.range N, deriv (fun t => A t k) 0 (referenceStep Q g k) := by
  -- All derivatives below belong to the actual raw executor and its true reached reference histories.
  let G := fun k t => probedGradient m (A t) (B t) g k
  have hG (k : ℕ) (hk : k ≤ N) : HasDerivAt (G k) (deriv (G k) 0) 0 :=
    ((smoothProbed_gradient_regular m hm A B (fun _ => g) 0 k
      (fun i hi => hA i (hi.trans_le hk)) (fun i hi => hB i (hi.trans_le hk)) contDiffAt_const
      Q hA0 hB0 hQ hpos (fun i hi => hpre i (hi.trans_le hk)) (hsmooth.mono m hk)).differentiableAt (by norm_num)).hasDerivAt
  have hstep (k : ℕ) (hk : k < N) :
      deriv (G (k+1)) 0-deriv (G k) 0=
        deriv (fun t => A t k) 0 (referenceStep Q g k)+Q (deriv (fun t => probedStep m (A t) (B t) g k) 0) := by
    -- Differentiate the exact recorded secant before dropping any genuine zero reference correction term.
    let s := fun t => probedStep m (A t) (B t) g k
    let χ := fun t => (probedPhase m (A t) (B t) g k).movement
    have hf := smoothProbed_fields_regular m hm A B (fun _ => g) 0 N hA hB contDiffAt_const
      Q hA0 hB0 hQ hpos hpre hsmooth k hk
    have hs := (hf.2.2.1.differentiableAt (by norm_num)).hasDerivAt
    have hχ := (hf.2.2.2.differentiableAt (by norm_num)).hasDerivAt
    have hs0 : s 0=referenceStep Q g k := by
      dsimp only [s]
      rw [hA0,hB0]
      exact quadratic_probedStep_eq_cg m hm Q hQ hpos g k
    have hχ0 : χ 0=0 := by
      obtain ⟨_,_,_,hz⟩ := hm Q hQ hpos g k
      dsimp only [χ,probedPhase]
      rw [hA0,hB0]
      exact (zeroCorrections_change_operator _ Q Q _ hz).2.1
    have hdA := ((hA k hk).differentiableAt (by norm_num)).hasDerivAt
    have hdB := ((hB k hk).differentiableAt (by norm_num)).hasDerivAt
    have hprod := (hdA.clm_apply hs).add ((hdB.sub hdA).clm_apply hχ)
    have heq : (fun t => G (k+1) t-G k t)=fun t => A t k (s t)+(B t k-A t k) (χ t) := by
      funext t
      have he := probedSecant_defect_identity m (A t) (B t) g k
      change (G (k+1) t-G k t)-A t k (s t)=(B t k-A t k) (χ t) at he
      exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
    have hleft := (hG (k+1) (by omega)).sub (hG k hk.le)
    change HasDerivAt (fun t => G (k+1) t-G k t) _ 0 at hleft
    rw [heq] at hleft
    have he := hleft.unique hprod
    change deriv (G (k+1)) 0-deriv (G k) 0=
      deriv (fun t => A t k) 0 (s 0)+A 0 k (deriv s 0)+
        ((deriv (fun t => B t k) 0-deriv (fun t => A t k) 0) (χ 0)+
          (B 0 k-A 0 k) (deriv χ 0)) at he
    rw [hs0,hχ0] at he
    simpa only [hA0,hB0,sub_self,map_zero,zero_apply,add_zero] using he
  -- Telescope the actual one-step derivative identities, including the genuinely empty horizon.
  have hsum : ∀ M ≤ N, deriv (G M) 0=
      Q (∑ k∈Finset.range M, deriv (fun t => probedStep m (A t) (B t) g k) 0)+
        ∑ k∈Finset.range M, deriv (fun t => A t k) 0 (referenceStep Q g k) := by
    intro M
    induction M with
    | zero => intro _;simp [G,probedGradient,methodRun]
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ,Finset.sum_range_succ,map_add]
      have hi := ih (by omega)
      have hs := hstep k (by omega)
      rw [hi] at hs
      exact (sub_eq_iff_eq_add.mp hs).trans (by abel)
  exact hsum N le_rfl

/-- Every actual smooth globally CG-consistent raw method has exactly the source genuine first-variation balance delta-g=A delta-x plus the true reference-step injection sum.
Use: Every actual smooth globally CG-consistent raw method has exactly the source genuine first-variation balance delta-g=A delta-x plus the true reference-step injection sum.
Article: main_krylov, apB:lem:filtration, actual raw-method gradient variation balance.
Proof: Use the actual complete-history displacement identity and its genuine differentiated finite step sum in the proved real executed gradient variation balance. All correction and search regularity and all true reference quantities have been discharged from primitive coefficients and actual CG consistency. -/
theorem probed_gradient_jet_balance (m : ProbedMethod E) (hm : CGConsistent m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q) (N : ℕ)
    (hA : ∀ k < N, ContDiffAt ℝ 2 (fun t => A t k) 0)
    (hB : ∀ k < N, ContDiffAt ℝ 2 (fun t => B t k) 0)
    (hpre : ∀ k < N, CG.gradient Q g k≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N) :
    deriv (fun t => probedGradient m (A t) (B t) g N) 0=
      Q (deriv (fun t => (methodRun m (A t) (B t) g N).displacement) 0)+
        ∑ k∈Finset.range N, deriv (fun t => A t k) 0 (referenceStep Q g k) := by
  -- Differentiate the genuine physical iterate, not a prescribed or surrogate displacement.
  have hfields := fun k hk => (smoothProbed_fields_regular m hm A B (fun _ => g) 0 N hA hB
    contDiffAt_const Q hA0 hB0 hQ hpos hpre hsmooth k hk).2.2.1
  have hsum := HasDerivAt.sum (fun k (hk : k∈Finset.range N) =>
    ((hfields k (Finset.mem_range.mp hk)).differentiableAt (by norm_num)).hasDerivAt)
  have hd : HasDerivAt (fun t => (methodRun m (A t) (B t) g N).displacement)
      (∑ k∈Finset.range N, deriv (fun t => probedStep m (A t) (B t) g k) 0) 0 := by
    convert hsum using 1
    funext t
    simp only [Finset.sum_apply]
    exact history_displacement_eq_steps m (A t) (B t) g N
  rw [hd.deriv]
  exact probed_gradient_jet_sum m hm A B g Q hQ hpos hA0 hB0 N hA hB hpre hsmooth

end
end krylov.Envelope
