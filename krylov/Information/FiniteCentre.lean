import krylov.Information.PhysicalCentre

/-!
Article: main_krylov, thm:centre and s4:cor-Q, genuine finite-horizon centre identities.
Use: actual source symmetry is needed only on the original finite
increment horizon; unqueried later source operators impose no extra premise.
Source: the proved exact latest-model flag telescoping identity applied to
constant continuation of the actual final probe and true physical transport.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The genuine latest-information probe error is the original old-block sum under exactly the source's finite increment symmetry assumptions.
Use: apply the actual physical centre theorem without a symmetry premise on any unqueried future operator.
Article: main_krylov, thm:centre and s4:cor-Q, actual finite-horizon information centre.
Proof: continue the true final probe constantly beyond the actual source horizon. Every real observed column and meaningful original increment is unchanged. The existing full flag telescoping theorem then has a genuine zero final artificial increment and yields precisely the stated original finite sum. -/
theorem Scenario.latest_probe_error_finite (S : Scenario (N+1))
    (hA : S.base.IsSymm) (hE : ∀ l<N, (S.increment l).IsSymm) :
    S.probe N-latest (observed S.probe)=S.oldPart N := by
  -- Preserve every genuine observed probe and replace only the irrelevant continuation by its true final value.
  let C := fun k => S.probe (min k N)
  have hCsym (k : ℕ) : (C k).IsSymm := by
    change (S.base+∑ l∈range (min k N), S.increment l)ᵀ=_
    simp only [transpose_add,transpose_sum,hA.eq]
    congr 1
    exact sum_congr rfl fun l hl => (hE l ((mem_range.mp hl).trans_le (min_le_right _ _))).eq
  have hf := model_error_eq_sum_compressions C hCsym
  have ho : observed C=observed S.probe := by
    ext i j
    change S.probe (min j.val N) i j=S.probe j.val i j
    rw [min_eq_left (by have := j.isLt; omega)]
  have hlast : C (N+1)=S.probe N := by simp only [C,min_eq_right (Nat.le_succ N)]
  have hzero : C (N+1)-C N=0 := by simp only [C,min_eq_right (Nat.le_succ N),min_self,sub_self]
  rw [hlast,ho,sum_range_succ,hzero,Matrix.mul_zero,Matrix.zero_mul,add_zero] at hf
  rw [hf]
  apply sum_congr rfl
  intro l hl
  have hlN := mem_range.mp hl
  simp only [C,min_eq_left (by omega : l+1≤N),min_eq_left hlN.le,S.probe_succ_sub]


/-- The true finite-horizon reflected terminal operator is exactly opposite the original terminal operator about the actual observed latest model.
Use: the original finite source symmetry constraints suffice for the common pre-quadratic centre.
Article: main_krylov, thm:centre and s4:cor-Q, actual finite-horizon information centre.
Proof: combine the original exact terminal reflection with the proved actual finite-horizon old-block model error. -/
theorem Scenario.reflect_about_latest_finite (S : Scenario (N+1))
    (hA : S.base.IsSymm) (hE : ∀ l<N, (S.increment l).IsSymm) :
    (S.reflect N).lastOperator N=(2 : ℝ) • latest (observed S.probe)-S.lastOperator N := by
  have h := S.latest_probe_error_finite hA hE
  rw [S.reflect_lastOperator]
  unfold Scenario.hiddenPart Scenario.lastOperator
  rw [← h]
  module


/-- The actual physical terminal reflection is about its genuine observed-data centre with symmetry required only on the original finite increment horizon.
Use: the common admissible pre-quadratic twin has the exact true opposite terminal error under original physical source assumptions.
Article: main_krylov, thm:centre and s4:cor-Q, actual finite-horizon information centre.
Proof: transport the proved finite-horizon terminal identity through the actual inverse direction congruence and recover the real observed physical model by the existing exact data theorem. -/
theorem Scenario.physical_reflect_about_centre_finite (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (hA : S.base.IsSymm) (hE : ∀ l<N, (S.increment l).IsSymm) :
    ((S.reflect N).inPhysical D).lastOperator N=
      (2 : ℝ) • S.physicalCentre D-(S.inPhysical D).lastOperator N := by
  simp only [Scenario.inPhysical,Scenario.mapForms_lastOperator,
    S.reflect_about_latest_finite hA hE,map_sub,map_smul]
  unfold Scenario.physicalCentre
  rw [S.physical_observed_data D hD]
  rfl

end
end krylov.Information
