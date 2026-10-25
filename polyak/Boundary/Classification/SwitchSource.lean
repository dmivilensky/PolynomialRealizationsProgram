import polyak.Boundary.Classification.SwitchData
import polyak.Boundary.Switches
import polyak.Boundary.P2.Arc
import polyak.Boundary.P2.Physical

/-! Exact source interpretation and refined algebraic root bounds for the switch decimals. -/
noncomputable section
namespace polyak.Boundary.Classification.SwitchSource
open LeanCert.Core LeanCert.Engine Numerics Numerics.Parametric SwitchData

/-- Fine enclosure of the actual cubic root, proved from source monotonicity and exact signs. -/
theorem G1_fine_bounds : (10332964166603/10000000000000 : ℝ)<G1 ∧
    G1<10332964166604/10000000000000 := by
  have hl : spiralSwitch (10332964166603/10000000000000 : ℝ)<0 := by norm_num [spiralSwitch]
  have hu : 0<spiralSwitch (10332964166604/10000000000000 : ℝ) := by norm_num [spiralSwitch]
  constructor
  · by_contra hn
    have hm := spiralSwitch_strictMonoOn.monotoneOn (show 1≤G1 by linarith [G1_bounds.1])
      (show (1 : ℝ)≤10332964166603/10000000000000 by norm_num) (le_of_not_gt hn)
    rw [spiralSwitch_G1] at hm
    linarith
  · by_contra hn
    have hm := spiralSwitch_strictMonoOn.monotoneOn
      (show (1 : ℝ)≤10332964166604/10000000000000 by norm_num)
      (show 1≤G1 by linarith [G1_bounds.1]) (le_of_not_gt hn)
    rw [spiralSwitch_G1] at hm
    linarith

/-- Fine enclosure of the actual degree-twelve root, with no floating-point premise. -/
theorem zetaA_fine_bounds : (16989316152393/10000000000000 : ℝ)<P2.zetaA ∧
    P2.zetaA<16989316152394/10000000000000 := by
  have hl : (16989316152393/10000000000000 : ℝ)∈P2.parameterInterval := by norm_num [P2.parameterInterval]
  have hu : (16989316152394/10000000000000 : ℝ)∈P2.parameterInterval := by norm_num [P2.parameterInterval]
  have hpl : 0<P2.N12 (16989316152393/10000000000000 : ℝ) := by norm_num [P2.N12]
  have hpu : P2.N12 (16989316152394/10000000000000 : ℝ)<0 := by norm_num [P2.N12]
  constructor
  · by_contra hn
    have hm := P2.N12_strictAntiOn.antitoneOn P2.zetaA_mem hl (le_of_not_gt hn)
    rw [P2.N12_zetaA] at hm
    linarith
  · by_contra hn
    have hm := P2.N12_strictAntiOn.antitoneOn hu P2.zetaA_mem (le_of_not_gt hn)
    rw [P2.N12_zetaA] at hm
    linarith

def parameter : Fin 3 → ℝ := ![Real.sqrt 3,G1,P2.zetaA]
def pointG : Fin 3 → ℝ := ![GW,G1,P2.Ga]
def pointU : Fin 3 → ℝ := ![1-1/(2*GW),1-1/(2*G1),P2.u P2.zetaA]

theorem parameter_mem (i : Fin 3) : parameter i∈parameterI i := by
  fin_cases i
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    norm_num [parameter,parameterI,IntervalRat.mem_def]
    constructor <;> nlinarith
  · norm_num [parameter,parameterI,IntervalRat.mem_def]
    constructor <;> linarith [G1_fine_bounds.1,G1_fine_bounds.2]
  · norm_num [parameter,parameterI,IntervalRat.mem_def]
    constructor <;> linarith [zetaA_fine_bounds.1,zetaA_fine_bounds.2]

theorem gExpr_eval (i : Fin 3) (ρ : ℕ → ℝ) (he : ρ 0=parameter i) :
    Expr.eval ρ (gExpr i)=pointG i := by
  fin_cases i
  · change ρ 0=Real.sqrt 3 at he
    norm_num [gExpr,SwitchData.gwE,SwitchData.half,pointG,Expr.eval,he,GW]
    ring
  · exact he
  · change ρ 0=P2.zetaA at he
    change Expr.eval ρ Certificates.Continuation.P5EndpointGraphs.G=P2.Ga
    rw [Certificates.Continuation.P5EndpointGraphs.G_exact,
      P2.RationalCode.expression_eval _ ρ (by rw [he]; exact P2.zetaA_mem),he]
    rfl

theorem uExpr_eval (i : Fin 3) (ρ : ℕ → ℝ) (he : ρ 0=parameter i) :
    Expr.eval ρ (uExpr i)=pointU i := by
  fin_cases i
  · change ρ 0=Real.sqrt 3 at he
    norm_num [uExpr,SwitchData.spiralU,SwitchData.gwE,SwitchData.half,pointU,Expr.eval,he,GW,
      div_eq_mul_inv,sub_eq_add_neg]
    ring
  · change ρ 0=G1 at he
    norm_num [uExpr,SwitchData.spiralU,pointU,Expr.eval,he,div_eq_mul_inv,sub_eq_add_neg]
  · change ρ 0=P2.zetaA at he
    change Expr.eval ρ Certificates.Continuation.P5EndpointGraphs.u=P2.u P2.zetaA
    rw [Certificates.Continuation.P5EndpointGraphs.u_exact,
      P2.RationalCode.expression_eval _ ρ (by rw [he]; exact P2.zetaA_mem),he]

/-- The three displayed endpoint source values are the true boundary at either sign of the exponent. -/
theorem endpoint_boundary (i : Fin 3) {t : ℝ} (ht : Real.cosh t=pointG i) :
    Spectral.V t=Real.arsinh (pointU i) := by
  fin_cases i
  · change Real.cosh t=GW at ht
    rw [spiral_optimal (by rw [ht]; exact G1_lt_GW.le) (by rw [ht]),ht]
    rfl
  · change Real.cosh t=G1 at ht
    rw [spiral_optimal (by rw [ht]) (by rw [ht]; exact G1_lt_GW.le),ht]
    rfl
  · exact P2.optimal P2.zetaA_mem P2.zeta1_lt_zetaA.le le_rfl ht

theorem pointG_ge_one (i : Fin 3) : 1≤pointG i := by
  fin_cases i
  · change 1≤GW
    linarith [GW_bounds.1]
  · change 1≤G1
    linarith [G1_bounds.1]
  · change 1≤P2.Ga
    linarith [P2.Ga_bounds.1]

def qPhysical (i : Fin 5) : ℝ :=
  (pointG (sourceIndex i)+(if positive i then 1 else -1)*Real.sqrt (pointG (sourceIndex i)^2-1))*
    (Real.sqrt (1+pointU (sourceIndex i)^2)-pointU (sourceIndex i))

theorem switchingQ_formula (i : Fin 5) : switchingQ i=qPhysical i := by
  have hcut : switchingExponent i=if positive i then Real.arcosh (pointG (sourceIndex i))
      else -Real.arcosh (pointG (sourceIndex i)) := by fin_cases i <;> rfl
  rw [switchingQ,hcut]
  cases hb : positive i
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [q_minus_formula (pointG_ge_one (sourceIndex i))
      (endpoint_boundary _ (by rw [Real.cosh_neg,Real.cosh_arcosh (pointG_ge_one _)]))]
    simp only [qPhysical,hb,Bool.false_eq_true,↓reduceIte,neg_one_mul,sub_eq_add_neg]
  · simp only [↓reduceIte]
    rw [q_plus_formula (pointG_ge_one (sourceIndex i))
      (endpoint_boundary _ (Real.cosh_arcosh (pointG_ge_one _)))]
    simp only [qPhysical,hb,↓reduceIte,one_mul]

end polyak.Boundary.Classification.SwitchSource
