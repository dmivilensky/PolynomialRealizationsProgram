import krylov.Stability.RFCRecordedOrders
import krylov.Envelope.ResidualOrders
import krylov.Methods.RFCProjection

/-!
Article: main_krylov, apD:prefix and thm:C, actual preterminal RFC residuals.
Use: extend the existing repeated-correction residual theorem to the initial
empty window and extract every actual chronological old-step pairing.
Source: reuse genuine RFC analyticity, the exact empty-window line search and
the proved zero-safe transfer from normalized to raw residual coordinates.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
/-- A higher power of the actual perturbation norm has every smaller nonnegative order locally.
Use: positive repeated-correction counts retain the quadratic old-residual bound needed by the incoming-vector expansion.
Article: main_krylov, thm:C2(b), passage from O(ω^(c+1)) to O(ω²).
Proof: on the actual unit neighborhood the nonnegative norm powers decrease with their exponent. -/
theorem norm_pow_order_mono {a b : ℕ} (hab : a≤b) :
    (fun z : X => ‖z‖^b) =O[𝓝 (0 : X)] (fun z => ‖z‖^a) := by
  apply IsBigO.of_bound 1
  filter_upwards [continuous_norm.continuousAt.eventually_lt_const
    (by norm_num : ‖(0 : X)‖<(1 : ℝ))] with z hz
  simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _),one_mul] using
    pow_le_pow_of_le_one (norm_nonneg z) hz.le hab

/-- The actual repeated RFC recorded residual order holds at every iteration, including the initial empty window.
Use: the preterminal induction no longer excludes the first actually evaluated step.
Article: main_krylov, apD:prefix, S_(k+1)ᵀg_(k+1)=O(ω^(c+1)).
Proof: positive iterations reuse the existing actual execution theorem. At
iteration zero the real RFC gate skips correction, and the exact line search
makes the true newly recorded step orthogonal to the returned gradient. -/
theorem recorded_projection_order (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hm : ∀ k, CG.gradient Q (g 0) k≠0 → 0<k → 0<memory k)
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod memory count (E := E)
    let V := fun z => (Fin.cons (probedStep m (A z) (B z) (g z) k)
      (fun i : Fin (min (memory k) k) => probedStep m (A z) (B z) (g z) (k-1-i.val)) :
        Fin (min (memory k) k+1) → E)
    (fun z => projectedResidual (unitWindow (V z))
      (probedGradient m (A z) (B z) (g z) (k+1))) =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+1)) := by
  -- Only the initial empty window needs a new argument; retain the original theorem at positive times.
  by_cases hk : 0<k
  · exact quadraticRFC_recorded_projected_order memory count A B g hA hB hg Q hA0 hB0 hQ hpos hm k hk hpre
  have hk0 : k=0 := by omega
  subst k
  let m := rfcMethod memory count (E := E)
  let H := fun z => methodRun m (A z) (B z) (g z) 0
  let d := fun z => m.direction (H z)
  have ht := quadraticRFC_prefix_analytic memory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    1 (fun i hi => hpre i (by omega))
  have hd : AnalyticAt ℝ d 0 := (ht.2 0 (by omega)).1
  have hz : AnalyticAt ℝ (fun z => A z 0 (d z)) 0 := analytic_operator_apply (hA 0) hd
  have hc : inner ℝ (d 0) (A 0 0 (d 0))≠0 := by
    have hd0 : d 0=CG.direction Q (g 0) 0 := by
      dsimp only [d,H]
      rw [hA0,hB0]
      exact rfc_reference_direction memory count Q hQ hpos (g 0) hm 0
    rw [hd0,hA0]
    exact (hpos _ (CG.invariant_line_pos Q hpos (g 0) 0
      (CG.invariant Q hQ hpos (g 0) 0 (by intro i hi; omega)) (hpre 0 le_rfl)).1).ne'
  have hcurv : ∀ᶠ z in 𝓝 (0 : X), inner ℝ (d z) (A z 0 (d z))≠0 :=
    (analytic_inner hd hz).continuousAt.eventually_ne hc
  apply IsBigO.of_bound 0
  filter_upwards [hcurv] with z hzc
  have he : selectedWindow memory (H z)=[] := by
    simp only [H,methodRun,selectedWindow,History.pairs,recordPairs,List.take_nil]
  have hr := rfc_empty_window_recorded_zero memory count (H z) (A z 0) (B z 0) (d z) rfl he hzc
  have hs : probedStep m (A z) (B z) (g z) 0=
      lineLength (H z).gradient (d z) (A z 0 (d z)) • d z := by
    have hq : rfcCorrection memory count (H z) (A z 0 (d z))=.done := by
      simp only [rfcCorrection,he,ne_eq,not_true_eq_false,false_and,ite_false]
    change _+(runCorrections (rfcCorrection memory count (H z) (A z 0 (d z)))
      (B z 0) (searchedGradient (H z).gradient (d z) (A z 0 (d z)))).movement=_
    rw [hq]
    exact add_zero _
  have hout : probedGradient m (A z) (B z) (g z) 1=
      (methodAdvance m (A z 0) (B z 0) (H z)).gradient := rfl
  have hv : (Fin.cons (probedStep m (A z) (B z) (g z) 0)
      (fun i : Fin (min (memory 0) 0) => probedStep m (A z) (B z) (g z) (0-1-i.val)) :
        Fin (min (memory 0) 0+1) → E)=fun _ => probedStep m (A z) (B z) (g z) 0 := by
    funext i
    have hi : i=0 := by
      apply Fin.ext
      have hlt := i.isLt
      simp only [Nat.min_zero] at hlt
      omega
    subst i
    rfl
  rw [hv,hout]
  have hproj : projectedResidual
      (unitWindow (fun _ : Fin (min (memory 0) 0+1) => probedStep m (A z) (B z) (g z) 0))
      (methodAdvance m (A z 0) (B z 0) (H z)).gradient=0 := by
    ext j
    change inner ℝ (‖probedStep m (A z) (B z) (g z) 0‖⁻¹ •
      probedStep m (A z) (B z) (g z) 0) _=0
    rw [hs]
    exact congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hr
  rw [hproj,norm_zero]
  simp only [zero_mul,le_refl]

/-- Every actual old-step/returned-gradient pairing in full-memory RFC has the proved repeated-correction order.
Use: the last incoming residual can now discard all old projected gradients to second order for ordinary RFC.
Article: main_krylov, apD:prefix, individual chronological residual coordinates.
Proof: the actual full recorded window has its proved normalized order at
every iteration; genuine analytic step columns allow zero-safe unnormalization
and the chronological age index selects precisely the requested real step. -/
theorem full_recorded_pair_order (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) (i : ℕ) (hi : i≤k) :
    (fun z => inner ℝ (probedStep (rfcMethod fullMemory count) (A z) (B z) (g z) i)
      (probedGradient (rfcMethod fullMemory count) (A z) (B z) (g z) (k+1))) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^(count+1)) := by
  -- The raw residual is one genuine chronological coordinate of the real full recorded window.
  let m := rfcMethod fullMemory count (E := E)
  let V := fun z (j : Fin (k+1)) => probedStep m (A z) (B z) (g z) (k-j.val)
  have hm : ∀ j, CG.gradient Q (g 0) j≠0 → 0<j → 0<fullMemory j := fun _ _ hj => hj
  have ht := quadraticRFC_prefix_analytic fullMemory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun j hj => hpre j (by omega))
  have hO := recorded_projection_order fullMemory count A B g hA hB hg Q hA0 hB0 hQ hpos hm k hpre
  dsimp only at hO
  rw [show min (fullMemory k) k=k from min_self k] at hO
  have hv (z : X) : (Fin.cons (probedStep m (A z) (B z) (g z) k)
      (fun j : Fin k => probedStep m (A z) (B z) (g z) (k-1-j.val)))=V z := by
    funext j
    refine Fin.cases rfl (fun l => ?_) j
    change probedStep m (A z) (B z) (g z) (k-1-l.val)=probedStep m (A z) (B z) (g z) (k-(l.val+1))
    congr 1
    omega
  have hO' : (fun z => projectedResidual (unitWindow (V z))
      (probedGradient m (A z) (B z) (g z) (k+1))) =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+1)) :=
    hO.congr_left fun z => by rw [hv]
  have hraw := krylov.Envelope.raw_residual_order V _ (fun z => ‖z‖^(count+1))
    (fun j => (ht.2 (k-j.val) (by omega)).2.1.continuousAt) hO' ⟨k-i,by omega⟩
  simpa only [V,show k-(k-i)=i by omega] using hraw

end
end krylov.Correction
