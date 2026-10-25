import chebyshev2.Filters.VolterraOperator
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Article: chebyshev2, Lemma 11.
Equation (43), including continuity and positivity of every Picard iterate.
Use: `chebyshev2.Filters.volterraTerm_properties` feeds `chebyshev2.Filters.jost_summable`
(jost summable).
Proof chain: `chebyshev2.HalfLine.jostProfile_boundary` — chebyshev2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/--
Defines `volterraTerm` by pattern matching with result type `ℕ → ℝ → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Filters.volterraTerm_properties` rewrites with this definition to
establish continuity of the displayed function: `Continuous (volterraTerm s m n) ∧ ∀ x,
volterraTerm s m n x ∈ Icc (0:ℝ) (factorialBound s (cumulative m x) n)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.jostProfile_boundary`.
-/
def volterraTerm (s : ℝ) (m : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n+1 => volterra s m (volterraTerm s m n)

/--
Defines `factorialBound` of type `ℝ` by `(s/2)^n*M^n/(n.factorial)`.

Use: `chebyshev2.Filters.factorialBound_mono` uses this definition to establish the stated
quantitative bound `factorialBound s M n ≤ factorialBound s N n`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.jostProfile_boundary`.
-/
def factorialBound (s M : ℝ) (n : ℕ) : ℝ := (s/2)^n*M^n/(n.factorial)

/--
The stated quantitative bound `0 ≤ factorialBound s M n`.

Use: `chebyshev2.LocalObstruction.volterra_power_norm` uses this bound to establish the
stated quantitative bound `‖(s • volterraMap hm)^n‖≤factorialBound s (∫ x,m x) n`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem factorialBound_nonneg {s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ factorialBound s M n := by unfold factorialBound; positivity

/--
The stated quantitative bound `factorialBound s M n ≤ factorialBound s N n`.

Use: `chebyshev2.Filters.volterraTerm_properties` uses this bound to establish continuity
of the displayed function: `Continuous (volterraTerm s m n) ∧ ∀ x, volterraTerm s m n x ∈ Icc
(0:ℝ) (factorialBound s (cumulative m x) n)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.jostProfile_boundary`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem factorialBound_mono {s M N : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M) (hMN : M ≤ N) (n : ℕ) :
    factorialBound s M n ≤ factorialBound s N n := by
  unfold factorialBound
  gcongr

/--
Exact identity `s/2*((s/2)^n/(n.factorial)*(M^(n+1)/(n+1)))=factorialBound s M (n+1)`.

Use: `chebyshev2.Filters.volterraTerm_properties` rewrites with this identity to establish
continuity of the displayed function: `Continuous (volterraTerm s m n) ∧ ∀ x, volterraTerm s m
n x ∈ Icc (0:ℝ) (factorialBound s (cumulative m x) n)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.jostProfile_boundary`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem factorialBound_step (s M : ℝ) (n : ℕ) :
    s/2*((s/2)^n/(n.factorial)*(M^(n+1)/(n+1)))=factorialBound s M (n+1) := by
  unfold factorialBound
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp
  ring

/--
Equation (43), including continuity and positivity of every Picard iterate.

Continuity of the displayed function: `Continuous (volterraTerm s m n) ∧ ∀ x, volterraTerm s m
n x ∈ Icc (0:ℝ) (factorialBound s (cumulative m x) n)`.

Use: `chebyshev2.Filters.jost_bounds` uses this continuity result to establish membership
in the specified domain/enclosure: `jost s m x ∈ Icc (1:ℝ) (exp (s*cumulative m x/2))`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.jostProfile_boundary`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem volterraTerm_properties {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : Continuous (volterraTerm s m n) ∧
      ∀ x, volterraTerm s m n x ∈ Icc (0:ℝ) (factorialBound s (cumulative m x) n) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero =>
    refine ⟨continuous_const,?_⟩
    intro x
    simp [volterraTerm,factorialBound]
  | succ n ih =>
    -- Establish hF as the integrability justification for the later integral estimates or
    -- changes of order.
    have hF : Integrable (fun t => m t*volterraTerm s m n t) := by
      apply bounded_forcing_integrable hm ih.1.aestronglyMeasurable (C := factorialBound s (∫ t, m t) n)
      intro t
      rw [Real.norm_eq_abs,abs_of_nonneg (ih.2 t).1]
      exact (ih.2 t).2 |>.trans (factorialBound_mono hs
        (cumulative_bounds hm hn t).1 (cumulative_bounds hm hn t).2 n)
    refine ⟨volterra_continuous hF s,?_⟩
    intro x
    have hnn (t : ℝ) : 0 ≤ m t*volterraTerm s m n t := mul_nonneg (hn t) (ih.2 t).1
    have hV := volterra_bounds hs hF hnn x
    refine ⟨hV.1,hV.2.trans ?_⟩
    have hdom : (∫ t in Iic x, m t*volterraTerm s m n t) ≤
        (s/2)^n/(n.factorial)*(cumulative m x)^(n+1)/(n+1) := by
      calc
        _ ≤ ∫ t in Iic x, (s/2)^n/(n.factorial)*(m t*(cumulative m t)^n) := by
          apply integral_mono_ae hF.integrableOn ((cumulative_power_integrable hm hn n).const_mul _).integrableOn
          exact Eventually.of_forall (fun t => by
            have he := mul_le_mul_of_nonneg_left (ih.2 t).2 (hn t)
            dsimp [factorialBound] at he
            convert he using 1; ring)
        _ = _ := by rw [integral_const_mul,cumulative_power_integral hm hn]; ring
    change s/2*cumulative (fun t => m t*volterraTerm s m n t) x ≤ _
    calc
      _ ≤ s/2*((s/2)^n/(n.factorial)*(cumulative m x)^(n+1)/(n+1)) :=
        mul_le_mul_of_nonneg_left hdom (by positivity)
      _ = factorialBound s (cumulative m x) (n+1) := by
        rw [← factorialBound_step s (cumulative m x) n]
        ring

end
end chebyshev2.Filters
