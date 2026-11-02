import krylov.Methods.SmoothProbedFields

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), genuine finite oracle-coordinate cycle charts.
Use: express real finite raw-method execution in actual finite operator
coordinates and derive its true primitive C-two output regularity for
transferring the genuine quadratic shadow first jet.
Source: actual full-history finite-prefix execution and the proved real
primitive smooth raw-policy regularity theorem.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine finite operator array extended after its true available horizon by the actual fixed reference operator.
Use: The genuine finite operator array extended after its true available horizon by the actual fixed reference operator.
Article: main_krylov, apB:lem:mu(c), genuine finite oracle-coordinate cycle charts.
Proof: Read actual finite indices before the horizon and use the true reference operator afterwards. -/
def finiteOracleExtension {N : ℕ} (Q : E →L[ℝ] E) (data : Fin N → E →L[ℝ] E) (k : ℕ) : E →L[ℝ] E :=
  if hk : k<N then data ⟨k,hk⟩ else Q

/-- The actual reference finite operator array extends exactly to the genuine constant reference operator sequence.
Use: The actual reference finite operator array extends exactly to the genuine constant reference operator sequence.
Article: main_krylov, apB:lem:mu(c), genuine finite oracle-coordinate cycle charts.
Proof: Every actual branch reads the same true reference operator. -/
theorem finiteOracleExtension_reference (N : ℕ) (Q : E →L[ℝ] E) :
    finiteOracleExtension Q (fun _ : Fin N => Q)=fun _ => Q := by
  funext k
  by_cases hk : k<N <;> simp only [finiteOracleExtension,hk,dite_true,dite_false]

/-- Actual finite raw-method execution depends only on its genuine first horizon-many line and correction operators.
Use: Actual finite raw-method execution depends only on its genuine first horizon-many line and correction operators.
Article: main_krylov, apB:lem:mu(c), genuine finite oracle-coordinate cycle charts.
Proof: Induct through the true complete-history executor, using actual equality of each real operator before the horizon. -/
theorem methodRun_congr_prefix (m : ProbedMethod E) (A B A' B' : ℕ → E →L[ℝ] E)
    (g : E) (N : ℕ) (hA : ∀ k<N, A k=A' k) (hB : ∀ k<N, B k=B' k) :
    methodRun m A B g N=methodRun m A' B' g N := by
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih (fun j hj => hA j (by omega)) (fun j hj => hB j (by omega)),hA k (by omega),hB k (by omega)]

/-- The actual extended finite operator chart executes exactly the genuine original method prefix.
Use: The actual extended finite operator chart executes exactly the genuine original method prefix.
Article: main_krylov, apB:lem:mu(c), genuine finite oracle-coordinate cycle charts.
Proof: The true finite chart agrees with every actual queried line and correction operator in that real prefix. -/
theorem finiteOracleExtension_run (m : ProbedMethod E) (Q : E →L[ℝ] E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (N : ℕ) :
    methodRun m (finiteOracleExtension Q (fun i : Fin N => A i.val))
      (finiteOracleExtension Q (fun i : Fin N => B i.val)) g N=methodRun m A B g N :=
  methodRun_congr_prefix m _ _ _ _ g N (fun _ hk => dite_eq_left hk) (fun _ hk => dite_eq_left hk)

/-- The genuine actual raw returned-gradient map is C-two in its true finite line and correction operator coordinates at every active positive quadratic reference.
Use: The genuine actual raw returned-gradient map is C-two in its true finite line and correction operator coordinates at every active positive quadratic reference.
Article: main_krylov, apB:lem:mu(c), genuine finite oracle-coordinate cycle charts.
Proof: Actual coordinate projections are smooth; use genuine primitive smooth-policy coefficient membership, real nonstagnation and true positive reference curvatures in the proved actual cycle regularity theorem. -/
theorem finiteOracle_gradient_regular (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0)
    (hsmooth : SmoothProbedCycleAt m 2 Q g N) :
    ContDiffAt ℝ 2 (fun p : (Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E) =>
      probedGradient m (finiteOracleExtension Q p.1) (finiteOracleExtension Q p.2) g N)
      ((fun _ => Q),(fun _ => Q)) := by
  -- Primitive coefficient membership derives the real cycle regularity on the actual finite operator-coordinate chart.
  apply smoothProbed_gradient_regular m hm
    (fun p : (Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E) => finiteOracleExtension Q p.1)
    (fun p => finiteOracleExtension Q p.2) (fun _ => g) ((fun _ => Q),(fun _ => Q)) N _ _ contDiffAt_const Q
    (finiteOracleExtension_reference N Q) (finiteOracleExtension_reference N Q) hQ hpos hpre hsmooth
  · intro k hk
    simp only [finiteOracleExtension,dite_eq_left hk]
    exact (contDiffAt_pi.mp contDiffAt_fst) (⟨k,hk⟩ : Fin N)
  · intro k hk
    simp only [finiteOracleExtension,dite_eq_left hk]
    exact (contDiffAt_pi.mp contDiffAt_snd) (⟨k,hk⟩ : Fin N)
end
end krylov.Methods
