import polyak.Boundary.P1.PhysicalContinuation
import polyak.Boundary.P2.Results
import polyak.Boundary.P5.Selection
import polyak.Boundary.P5.LocalLimits

/-! Source functions of the four-arc classification, fixed before their global identification. -/
noncomputable section
namespace polyak.Boundary.Classification
open Spectral

def p2Parameter (G : ℝ) : ℝ := by
  classical
  exact if h : G∈Set.Icc P2.Ga G1 then (P2.existsUnique_parameter h).choose else P2.zeta1

theorem p2Parameter_spec {G : ℝ} (hG : G∈Set.Icc P2.Ga G1) :
    p2Parameter G∈Set.Icc P2.zeta1 P2.zetaA ∧ P2.G (p2Parameter G)=G := by
  classical
  simp only [p2Parameter,dite_eq_left hG]
  exact (P2.existsUnique_parameter hG).choose_spec.1

theorem p2Parameter_unique {G z : ℝ} (hG : G∈Set.Icc P2.Ga G1)
    (hz : z∈Set.Icc P2.zeta1 P2.zetaA) (he : P2.G z=G) : p2Parameter G=z := by
  have hp := p2Parameter_spec hG
  exact P2.G_strictAntiOn.injOn (P2.arc_mem_interval hp.1) (P2.arc_mem_interval hz)
    (hp.2.trans he.symm)

/-- The regular one-atom source family in its physical G coordinate. -/
def u1 (G : ℝ) : ℝ := P1.branchU (1/G) (P1.continuation (1/G) 0)
/-- The unique rational two-atom source family in its physical G coordinate. -/
def u2 (G : ℝ) : ℝ := P2.u (p2Parameter G)
/-- The actual checked regularized central source family. -/
def u5 (G : ℝ) : ℝ := P5.branchU (G-1) (P5.Selection.continuation (G-1))

/-- Article: the complete four-arc piecewise twist. -/
def u (G : ℝ) : ℝ :=
  if G≤P2.Ga then u5 G else if G≤G1 then u2 G else if G≤GW then 1-1/(2*G) else u1 G

theorem p1_parameter {t : ℝ} (hG : GW≤Real.cosh t) :
    1/Real.cosh t∈Set.Ioc (0 : ℝ) P1.zW := by
  refine ⟨by positivity,?_⟩
  unfold P1.zW
  exact one_div_le_one_div_of_le (by linarith [GW_bounds.1]) hG

theorem p1_formula {t : ℝ} (hG : GW≤Real.cosh t) : V t=Real.arsinh (u1 (Real.cosh t)) := by
  have ht : Real.cosh t=1/(1/Real.cosh t) := by field_simp
  exact P1.continuation_optimal (p1_parameter hG) ht

theorem p2_formula {t : ℝ} (hG : Real.cosh t∈Set.Icc P2.Ga G1) :
    V t=Real.arsinh (u2 (Real.cosh t)) := by
  have hp := p2Parameter_spec hG
  exact P2.optimal (P2.arc_mem_interval hp.1) hp.1.1 hp.1.2 hp.2.symm

/-- Exact common source coordinate at the spiral-to-P2 join. -/
theorem u2_G1 : u2 G1=1-1/(2*G1) := by
  have hG : G1∈Set.Icc P2.Ga G1 := ⟨P2.Ga_lt_G1.le,le_rfl⟩
  unfold u2
  rw [p2Parameter_unique hG ⟨le_rfl,P2.zeta1_lt_zetaA.le⟩ P2.G_zeta1]
  exact P2.u_zeta1

/-- Exact common source coordinate at the P1-to-spiral radical join. -/
theorem u1_GW : u1 GW=1-1/(2*GW) := by
  unfold u1
  change P1.branchU P1.zW (P1.continuation P1.zW 0)=_
  rw [P1.continuation_endpoint]
  have h := P1.endpoint_spiral_formulas
  exact h.1

end polyak.Boundary.Classification
