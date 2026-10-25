import polyak.Boundary.SpiralArc

/-! Article: exact outer endpoint G_W of the spiral arc, with an isolated algebraic root. -/
namespace polyak.Boundary
noncomputable section
open Polynomial

/-- Article: the source quadratic defining the outer spiral endpoint. -/
def spiralOuterPolynomial : ℚ[X] := C 2*X^2-C 2*X-C 1

/-- Article: exact equation of the displayed radical G_W=(1+√3)/2. -/
theorem GW_equation : 2*GW^2-2*GW-1=0 := by
  have hs:=Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold GW
  nlinarith

/-- Article: a strict rational isolation interval for the exact radical endpoint. -/
theorem GW_bounds : (683/500 : ℝ)<GW ∧ GW<13661/10000 := by
  have hs:=Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn:=Real.sqrt_nonneg (3 : ℝ)
  unfold GW
  constructor <;> nlinarith

/-- Article: the physical root of the outer endpoint equation is unique. -/
theorem GW_unique {v : ℝ} (hv : 1 ≤ v) (he : 2*v^2-2*v-1=0) : v=GW := by
  have hp : 0<v+GW-1 := by linarith [GW_bounds.1]
  have hf : (v-GW)*(v+GW-1)=0 := by nlinarith [GW_equation]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp.ne')

/-- Article: the dual weight vanishes at the exact outer endpoint. -/
theorem spiralWeight_GW : spiralWeight GW=0 := by
  unfold spiralWeight
  rw [show 1+2*GW-2*GW^2=0 by linarith [GW_equation]]
  simp

/-- Article: this is the unique physical zero of the spiral weight. -/
theorem spiralWeight_eq_zero_iff {v : ℝ} (hv : 1 ≤ v) : spiralWeight v=0 ↔ v=GW := by
  constructor
  · intro he
    have hd : 4*v+1≠0 := by linarith
    unfold spiralWeight at he
    have hn := (div_eq_zero_iff).mp he
    rcases hn with hn|hn
    · apply GW_unique hv
      nlinarith
    · exact False.elim (hd hn)
  · intro he
    rw [he]
    exact spiralWeight_GW

/-- Article: the independent rational enclosure of G_W. -/
def GWInterval : LeanCert.Core.IntervalRat := ⟨683/500,13661/10000,by norm_num⟩

/-- Article: the actual radical, exact source equation, and uniqueness form an isolated root. -/
def GWRoot : Numerics.IsolatedRoot spiralOuterPolynomial GWInterval where
  value := GW
  mem := by
    rw [LeanCert.Core.IntervalRat.mem_def]
    norm_num [GWInterval]
    exact ⟨GW_bounds.1.le,GW_bounds.2.le⟩
  root := by
    norm_num [spiralOuterPolynomial,Polynomial.aeval_def]
    exact GW_equation
  unique v hv he := by
    apply GW_unique
    · rw [LeanCert.Core.IntervalRat.mem_def] at hv
      have h:=hv.1
      norm_num [GWInterval] at h
      linarith
    · simpa [spiralOuterPolynomial,Polynomial.aeval_def] using he

/-- Article: the designated spiral-to-P₂ cubic root is the only real root. -/
theorem G1_unique_real {v : ℝ} (hv : spiralSwitch v=0) : v=G1 := by
  have hv1 : 1<v := by
    by_cases hv0 : v ≤ 0
    · have hc:=mul_nonpos_of_nonneg_of_nonpos (sq_nonneg v) hv0
      unfold spiralSwitch at hv
      nlinarith [sq_nonneg v]
    · have hp : 0<v := lt_of_not_ge hv0
      by_contra hh
      have hu : v ≤ 1 := le_of_not_gt hh
      have hf : spiralSwitch v= -(2*v-1)^2-32*v^2*(1-v) := by unfold spiralSwitch; ring
      have hn : 0 ≤ 32*v^2*(1-v) := mul_nonneg (by positivity) (by linarith)
      rw [hf] at hv
      have hs : (2*v-1)^2=0 := by nlinarith [sq_nonneg (2*v-1)]
      have he := sq_eq_zero_iff.mp hs
      have hvhalf : v=1/2 := by linarith
      subst v
      norm_num at hv
  apply spiralSwitch_strictMonoOn.injOn hv1.le (show 1 ≤ G1 by linarith [G1_bounds.1])
  exact hv.trans spiralSwitch_G1.symm

/-- Article: the independently designated spiral switch is a simple cubic root. -/
theorem G1_simple : aeval G1 spiralSwitchPolynomial.derivative≠0 := by
  have hp : 0<aeval G1 spiralSwitchPolynomial.derivative := by
    norm_num [spiralSwitchPolynomial,Polynomial.aeval_def]
    nlinarith [G1_bounds.1,sq_nonneg (G1-1)]
  exact hp.ne'

end
end polyak.Boundary
