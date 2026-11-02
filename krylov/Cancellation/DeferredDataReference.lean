import krylov.Cancellation.DCSlide
set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and thm:DC, actual data-dependent deferred reference.
Use: extend genuine global quadratic history/CG consistency to the original
data-only final estimate, including every true solved tail and memory regime.
Source: actual zero observed reference residuals, true data-dependent tilted
solve and the proved genuine FC complete quadratic history.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original data-dependent deferred policy has exactly the FC direction
on every true quadratic reference history, regardless of its estimate value.
Use: native consistency is a theorem of actual observed residual cancellation.
Article: main_krylov, s3:def:DC and thm:DC.
Proof: the genuine fixed horizon selects either the real FC direction or the
actual tilted solve; true zero reference residuals remove the latter tilt. -/
theorem deferred_data_reference_direction (memory : ℕ → ℕ) (horizon : ℕ) (estimate : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hp : H.pairs=referencePairs Q g k) (hg : H.gradient=CG.gradient Q g k) :
    (deferredDataMethod memory horizon estimate).direction H=(fcMethod memory).direction H := by
  change (if H.records.length+1=horizon then dcSlideDirection memory estimate H else (fcMethod memory).direction H)=_
  split_ifs
  · exact dc_slide_reference_direction memory estimate Q hQ hpos g k H hp hg
  · rfl

/-- The real arbitrary-estimate deferred implementation has the entire true
quadratic FC history, including all actual observations and solved tails.
Use: original final estimates may depend on all genuinely observed data.
Article: main_krylov, s3:def:DC and thm:DC.
Proof: real finite execution induction uses genuine FC reference transcripts
to remove the actual data-dependent tilt before each native search. -/
theorem deferred_data_reference_run (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (horizon : ℕ) (estimate : History E → ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) g k=
      methodRun (fcMethod memory) (fun _ => Q) (fun _ => Q) g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih]
    have hs := fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k
    have hd := deferred_data_reference_direction memory horizon estimate Q hQ hpos g k _ hs.2 hs.1
    unfold methodAdvance
    rw [hd]
    rfl

/-- Original data-dependent deferred cancellation is globally CG-consistent
for every positive newest-retaining memory, with true solved tails included.
Use: the actual source implementation satisfies the genuine raw information class.
Article: main_krylov, s3:def:DC and thm:DC.
Proof: transfer genuine FC consistency through full actual history equality
and the proved real zero-reference-tilt direction identity. -/
theorem deferred_data_consistent (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (horizon : ℕ) (estimate : History E → ℝ) : CGConsistent (deferredDataMethod memory horizon estimate) := by
  intro Q hQ hpos g k
  have hs := fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k
  obtain ⟨c,hc,hd,_⟩ := fcMethod_consistent memory hm Q hQ hpos g k
  refine ⟨c,hc,?_,by trivial⟩
  rw [deferred_data_reference_run memory hm horizon estimate Q hQ hpos g k,
    deferred_data_reference_direction memory horizon estimate Q hQ hpos g k _ hs.2 hs.1]
  exact hd

end
end krylov.Cancellation
