import krylov.Functions.PlanarUniformBounds
import krylov.Functions.PlanarFunctionMinimax

/-!
Article: main_krylov, thm:Fplanar, the actual finite-scale centre policy.
Use: construct one observation-only output for the genuine cubic functions
and retain the exact minimax leading coefficient with a uniform fourth-order
error. Source: actual compact interval fibres and exact polynomial Taylor
identities. No regularity of the fibre-centre policy is required.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace ENNReal

/-- The actual observed-fibre centre is an admissible tensor whenever that
fibre is nonempty. Article: main_krylov, thm:Fplanar. -/
theorem fibreCentre_mem (r : ℝ) (O : Observation) (hne : (coefficientFibre r O).Nonempty) :
    fibreCentre r O∈coefficientFibre r O := by
  have hc := coefficientFibre_isCompact r O
  have hlo := hc.sInf_mem hne
  have hhi := hc.sSup_mem hne
  have horder := csInf_le hc.bddBelow hhi
  rw [coefficientFibre_eq_Icc r O hne]
  change sInf (coefficientFibre r O)≤(sInf (coefficientFibre r O)+sSup (coefficientFibre r O))/2 ∧
    (sInf (coefficientFibre r O)+sSup (coefficientFibre r O))/2≤sSup (coefficientFibre r O)
  constructor <;> linarith only [horder]

/-- The true completion chosen by the explicit observation-only centre rule.
Article: main_krylov, thm:Fplanar. -/
def planeCentreTensor (r : ℝ) (O : Observation) : krylov.Tensor.BinaryCubic :=
  complete r O (fibreCentre r O)

/-- Every genuine observed fibre has an actual admissible centre completion.
Article: main_krylov, thm:Fplanar. -/
theorem planeCentreTensor_inBall {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) (r : ℝ) :
    (planeCentreTensor r (observe r t)).InBall :=
  fibreCentre_mem r (observe r t) ⟨t.t2,self_mem_coefficientFibre ht r⟩

/-- The explicit finite-scale output using only the actual observed coefficients.
Article: main_krylov, thm:Fplanar, attained centring upper bound. -/
def planeCentreOutput (r p : ℝ) (O : Observation) : Plane :=
  let t := planeCentreTensor r O
  let ρ := planeTerminalRho r t
  planeOfPair (p,r*p)-p^2 • ρ+p^3 • planeTerminalOperator r t ρ

/-- The actual leading discrepancy of the centre rule is bounded by the
sharp full information radius, with the original Euclidean constant.
Article: main_krylov, thm:Fplanar. -/
theorem planeCentre_leading_bound {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) (r : ℝ) :
    ‖(planeTerminalOperator r (planeCentreTensor r (observe r t))-planeTerminalOperator r t)
        (planeTerminalRho r t)‖≤r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r := by
  let O := observe r t
  let u := planeCentreTensor r O
  have hobs : observe r t=observe r u := by exact (observe_complete r O (fibreCentre r O)).symm
  rw [planeTerminal_difference_rho r t u hobs,norm_smul,Real.norm_eq_abs,planarFibreDirection_norm]
  have hq := self_mem_coefficientFibre ht r
  have hhalf := fibreCentre_bound hq
  have hmf := fibreProduct_le_minimax r O ⟨t.t2,hq⟩
  have he : |(u.t2-t.t2)*r^2*(t.t1+r*t.t2)/4|=
      r^2/4*|O.P| *|t.t2-fibreCentre r O| := by
    simp only [u,planeCentreTensor,complete,abs_div,abs_mul,abs_of_nonneg (sq_nonneg r)]
    rw [show |(4:ℝ)|=4 by norm_num,abs_sub_comm]
    change |t.t2-fibreCentre r O| * r^2*|O.P|/4=r^2/4*|O.P| *|t.t2-fibreCentre r O|
    ring
  rw [he]
  calc
    _ ≤ r^2/4*(|O.P| *fibreHalfWidth r O)*Real.sqrt (1+4*r^2) := by
      have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : 0≤r^2/4*|O.P|)
      exact (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _)).trans_eq (by ring)
    _ ≤ r^2/4*fibreMinimax r*Real.sqrt (1+4*r^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmf (by positivity)) (Real.sqrt_nonneg _)
    _ = _ := by ring

end
end krylov.Functions
