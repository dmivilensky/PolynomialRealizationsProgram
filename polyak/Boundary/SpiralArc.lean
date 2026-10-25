import polyak.Boundary.P2.Weights
import polyak.Numerics.Root

/-!
Article: the spiral certificate and its exact optimality interval.
Use: the two endpoints are algebraic numbers with certified rational enclosures.
Proof: an explicit quartic factorization and the completed-square residual.
-/

namespace polyak.Boundary
noncomputable section
open Spectral Polynomial

/-- Article: the algebraic switch G_W=(1+sqrt 3)/2. -/
def GW : ℝ := (1+Real.sqrt 3)/2

/-- Article: the cubic defining G₁. -/
def spiralSwitch (G : ℝ) : ℝ := 32*G^3-36*G^2+4*G-1

/-- Article: the independent rational-polynomial source of the switch cubic. -/
def spiralSwitchPolynomial : ℚ[X] := C 32*X^3-C 36*X^2+C 4*X-1

/-- Article: exact rational isolating interval for G₁. -/
def G1Interval : LeanCert.Core.IntervalRat := ⟨103329/100000,10333/10000,by norm_num⟩

/-- Article: an actual unique root in the printed transition enclosure. -/
theorem exists_G1 : Nonempty (Numerics.IsolatedRoot spiralSwitchPolynomial G1Interval) := by
  apply Numerics.exists_isolatedRoot G1Interval
  · norm_num [G1Interval,spiralSwitchPolynomial]
  · norm_num [G1Interval,spiralSwitchPolynomial]
  · intro G hG
    rw [LeanCert.Core.IntervalRat.mem_def] at hG
    have hg : 1 ≤ G := by norm_num [G1Interval] at hG; linarith [hG.1]
    have hp : 0 ≤ G*(G-1) := mul_nonneg (by linarith) (by linarith)
    norm_num [spiralSwitchPolynomial]
    nlinarith

/-- Article: the designated exact root G₁. -/
def G1Root : Numerics.IsolatedRoot spiralSwitchPolynomial G1Interval := Classical.choice exists_G1

/-- Article: the spiral-to-P₂ switching value. -/
def G1 : ℝ := G1Root.value

/-- Article: certified enclosure of G₁. -/
theorem G1_bounds : 103329/100000 < G1 ∧ G1 < 10333/10000 := by
  have hm := G1Root.mem
  have hr := G1Root.root
  rw [LeanCert.Core.IntervalRat.mem_def] at hm
  norm_num [G1Interval] at hm
  change 103329/100000 ≤ G1 ∧ G1 ≤ 10333/10000 at hm
  have he : spiralSwitch G1=0 := by simpa [spiralSwitchPolynomial,spiralSwitch,G1] using hr
  constructor
  · apply lt_of_le_of_ne hm.1
    intro hh
    rw [← hh] at he
    norm_num [spiralSwitch] at he
  · apply lt_of_le_of_ne hm.2
    intro hh
    rw [hh] at he
    norm_num [spiralSwitch] at he

/-- Article: the defining cubic equation holds at G₁. -/
theorem spiralSwitch_G1 : spiralSwitch G1=0 := by
  simpa [spiralSwitchPolynomial,spiralSwitch,G1] using G1Root.root

/-- Article: monotonicity of the switch cubic on the complete physical half-line. -/
theorem spiralSwitch_strictMonoOn : StrictMonoOn spiralSwitch (Set.Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (1 : ℝ))
  · exact (by unfold spiralSwitch; fun_prop : Continuous spiralSwitch).continuousOn
  · intro G hG
    have hg : 1 ≤ G := interior_subset hG
    have hd : HasDerivAt spiralSwitch (96*G^2-72*G+4) G := by
      convert ((((hasDerivAt_id G).pow 3).const_mul 32).sub
        (((hasDerivAt_id G).pow 2).const_mul 36)).add
          ((hasDerivAt_id G).const_mul 4) |>.sub_const 1 using 1
      · funext x
        dsimp [spiralSwitch]
      · norm_num
        ring
    rw [hd.deriv]
    have hp := mul_nonneg (show 0 ≤ G by linarith) (show 0 ≤ G-1 by linarith)
    nlinarith

/-- Article: nonnegative residual constant throughout the spiral optimality arc. -/
theorem spiralSwitch_nonneg {G : ℝ} (hG : G1 ≤ G) : 0 ≤ spiralSwitch G := by
  rw [← spiralSwitch_G1]
  exact spiralSwitch_strictMonoOn.monotoneOn (show 1 ≤ G1 by linarith [G1_bounds.1])
    (show 1 ≤ G by linarith [G1_bounds.1]) hG

/-- Article: the exact upper-lag-two multiplier on the spiral. -/
def spiralWeight (G : ℝ) : ℝ := 2*(1+2*G-2*G^2)/(4*G+1)

/-- Article: the spiral weight belongs to the simplex throughout [1,G_W]. -/
theorem spiralWeight_mem {G : ℝ} (hG : 1 ≤ G) (hGW : G ≤ GW) :
    0 ≤ spiralWeight G ∧ spiralWeight G ≤ 1 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hbound : 2*G-1 ≤ Real.sqrt 3 := by unfold GW at hGW; linarith
  have hprod : 0 ≤ (Real.sqrt 3-(2*G-1))*(Real.sqrt 3+(2*G-1)) :=
    mul_nonneg (by linarith) (by linarith)
  have hn : 0 ≤ 1+2*G-2*G^2 := by nlinarith
  unfold spiralWeight
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · apply (div_le_one (by positivity : 0 < 4*G+1)).mpr
    nlinarith

/-- Article: the remaining quadratic in the exact spiral certificate. -/
def spiralResidual (G c : ℝ) : ℝ := 2*G*c^2-(2*G-1)*c+4*G*(G-1)

/-- Article: exact completed square exposing the switch cubic. -/
theorem spiralResidual_square {G : ℝ} (hG : G≠0) (c : ℝ) :
    spiralResidual G c=2*G*(c-(2*G-1)/(4*G))^2+spiralSwitch G/(8*G) := by
  unfold spiralResidual spiralSwitch
  field_simp
  ring

/-- Article: the residual quadratic is nonnegative throughout the exact spiral arc. -/
theorem spiralResidual_nonneg {G : ℝ} (hG : G1 ≤ G) (c : ℝ) : 0 ≤ spiralResidual G c := by
  have hg : 0 < G := by linarith [G1_bounds.1]
  rw [spiralResidual_square (ne_of_gt hg)]
  exact add_nonneg (by positivity) (div_nonneg (spiralSwitch_nonneg hG) (by positivity))

/-- Article: the full exact spiral symbol factorization, retaining the actual normalized weights. -/
theorem spiralSymbol_factor {G : ℝ} (hG : 1 ≤ G) (hGW : G ≤ GW) (c : ℝ) :
    dualSymbol (weights23 (spiralWeight G) (spiralWeight_mem hG hGW).1
      (spiralWeight_mem hG hGW).2) (1-1/(2*G)) G c=
      -(G-c)*(2*G*c+1)^2*spiralResidual G c/(2*G^3*(4*G+1)) := by
  have hg : G≠0 := by linarith
  have hd : 4*G^2-1≠0 := by nlinarith
  have hd' : G^2*4-1≠0 := by nlinarith
  have hw : 4*G+1≠0 := by linarith
  rw [dualSymbol_weights23_factor _ _ _ hG]
  unfold spiralWeight cubicAlpha quadraticBeta spiralResidual
  field_simp [hg,hd,hd',hw]
  ring

/-- Article: the spiral achieves the exact spectral boundary on [G₁,G_W]. -/
theorem spiral_optimal {t : ℝ} (hG : G1 ≤ Real.cosh t) (hGW : Real.cosh t ≤ GW) :
    V t=Real.arsinh (1-1/(2*Real.cosh t)) := by
  have hg := Real.one_le_cosh t
  let w := weights23 (spiralWeight (Real.cosh t)) (spiralWeight_mem hg hGW).1
    (spiralWeight_mem hg hGW).2
  apply primal_dual_optimal w (u := 1-1/(2*Real.cosh t))
  · have hc := Real.cosh_pos t
    have hdiv : 1/(2*Real.cosh t) ≤ 1/2 := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2*Real.cosh t) (by norm_num : (0 : ℝ) < 2)).mpr
      linarith
    linarith
  · exact Spiral.feasibleU t
  · intro c
    have hn : dualSymbol w (1-1/(2*Real.cosh t)) (Real.cosh t) c ≤ 0 := by
      rw [show w=weights23 (spiralWeight (Real.cosh t)) (spiralWeight_mem hg hGW).1
        (spiralWeight_mem hg hGW).2 from rfl,spiralSymbol_factor hg hGW]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (show 0 ≤ Real.cosh t-c from sub_nonneg.mpr (c.property.2.trans hg)))
            (sq_nonneg _)) (spiralResidual_nonneg hG c)) (by positivity)
    have hgap : 0 < Real.cosh t-(c : ℝ) := by linarith [G1_bounds.1,c.property.2]
    rw [dualPolynomial_factor w _ hg] at hn
    nlinarith

end
end polyak.Boundary
