import krylov.OneGradient.InformedPhysicalScenario
import krylov.OneGradient.ScenarioOperators
import krylov.Stability.MetricRootRegularity
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), true physical attaining operator family.
Use: derive every native expansion hypothesis directly for the genuine
original admissible physical source scenarios, before computing output.
Source: actual affine last-Lanczos base, exact source operator extension
and genuine physical root-congruence increments and output form.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Information krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine original physical sharpness family is C-one in its real
scale, all reference operators are the known base, and all operators are
symmetric from the primitive source witness data.
Use: the actual native output cubic theorems apply to these real admissible
source executions; no smooth path or trajectory is supplied separately.
Article: main_krylov, thm:local(b), primitive physical attainer regularity.
Proof: the actual prior base is its explicit affine last-Lanczos physical
rank-one change. Every original physical increment and terminal form is
an affine real-scale root congruence. Finite actual source probes and the
independent output extension preserve C-one regularity and symmetry. -/
theorem informedPhysicalScenario_operator_data
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hD : ∀ l<n,(D l).IsSymm) (hF : F.IsSymm) (c : ℝ) :
    let M := fun t j => oneGradientScenarioMatrices (informedPhysicalScenario A hA g hg hc D F c t) n j
    (∀ j,ContDiffAt ℝ 1 (fun t : ℝ => M t j) 0) ∧
      (∀ t j,(M t j).IsSymm) ∧ ∀ j,M 0 j=A := by
  let S := fun t => informedPhysicalScenario A hA g hg hc D F c t
  let B := fun t => informedPriorBase A hA g hg hc (c*t)
  have hB : ContDiffAt ℝ 1 B 0 := by
    change ContDiffAt ℝ 1 (fun t : ℝ => A+
      ((lastJacobiPivot A hA g hg hc+c*t/lastInversePivot A hA g hg hc)-lastJacobiPivot A hA g hg hc) •
        vecMulVec (WithLp.ofLp (lastLanczosVector A hA g hg hc))
          (WithLp.ofLp (lastLanczosVector A hA g hg hc))) 0
    exact contDiffAt_const.add ((contDiffAt_const.add
      ((contDiffAt_const.mul contDiffAt_id).div_const _)).sub contDiffAt_const |>.smul contDiffAt_const)
  have hinc (l : ℕ) : ContDiffAt ℝ 1 (fun t : ℝ => (S t).increment l) 0 :=
    (contDiffAt_const.mul (contDiffAt_id.smul contDiffAt_const)).mul contDiffAt_const
  have hterm : ContDiffAt ℝ 1 (fun t : ℝ => (S t).terminal) 0 :=
    (contDiffAt_const.mul (contDiffAt_id.smul contDiffAt_const)).mul contDiffAt_const
  have hprobe (j : ℕ) : ContDiffAt ℝ 1 (fun t : ℝ => (S t).probe j) 0 :=
    hB.add (ContDiffAt.sum (fun l _ => hinc l))
  have hBsym (t : ℝ) : (B t).IsSymm := by
    have hr : (vecMulVec (WithLp.ofLp (lastLanczosVector A hA g hg hc))
        (WithLp.ofLp (lastLanczosVector A hA g hg hc))).IsSymm := by
      rw [Matrix.IsSymm,Matrix.transpose_vecMulVec]
    exact hA.1.isSymm.add (hr.smul _)
  have hs (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hM : M.IsSymm) (t : ℝ) :
      (metricRoot A*(t • M)*metricRoot A).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.transpose_mul,(metricRoot_isSymm A).eq,
      Matrix.transpose_smul,hM.eq,Matrix.mul_assoc]
  have hpsym (t : ℝ) (j : ℕ) (hj : j≤n) : ((S t).probe j).IsSymm :=
    (hBsym t).add (by
      rw [Matrix.IsSymm,Matrix.transpose_sum]
      apply sum_congr rfl
      intro l hl
      exact (hs (D l) (hD l ((mem_range.mp hl).trans_le hj)) t).eq)
  refine ⟨?_,?_,?_⟩
  · intro j
    by_cases hj : j≤n
    · simpa only [oneGradientScenarioMatrices,ite_eq_left hj] using hprobe j
    · simpa only [oneGradientScenarioMatrices,ite_eq_right hj,Scenario.lastOperator] using (hprobe n).add hterm
  · intro t j
    by_cases hj : j≤n
    · change (oneGradientScenarioMatrices (S t) n j).IsSymm
      rw [oneGradientScenarioMatrices_probe (S t) n j hj]
      exact hpsym t j hj
    · change (if j≤n then (S t).probe j else (S t).probe n+(S t).terminal).IsSymm
      rw [ite_eq_right hj]
      exact (hpsym t n le_rfl).add (hs F hF t)
  · intro j
    simp only [oneGradientScenarioMatrices,informedPhysicalScenario,informedPriorBase,lanczosCompletion,
      mul_zero,zero_div,zero_smul,Matrix.zero_mul,Scenario.probe,Scenario.lastOperator,
      sum_const_zero,add_zero,sub_self,ite_self]

end
end krylov.OneGradient
