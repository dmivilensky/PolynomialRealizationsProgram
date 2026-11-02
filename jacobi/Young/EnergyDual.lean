import jacobi.Young.Sharp
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
A finite-energy source acts continuously on the existing exact H1 space.
The elementary H1-to-L3 bound and Holder construct its genuine continuous
dual functional even when the source is not integrable in L1. Riesz then
constructs the actual Green potential in GeneralPotential, allowing equality
classification in the full scope of the printed theorem.
Source: Holder and the Hilbert-space Riesz representation theorem (mathlib).
Use: a finite L^(3/2) source defines a bounded linear functional on the actual H1 space.
-/
namespace jacobi.Young
noncomputable section
open Real MeasureTheory Filter chebyshev2.Sobolev
open scoped InnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Every exact H1 representative has an integrable absolute cube with a homogeneous norm bound.
Use: a finite L^(3/2) source defines a bounded linear functional on the actual H1 space.
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: the already proved H1 point-evaluation and integral energy bounds.
Proof: |u|≤norm(u), and the squared integral is at most norm(u)²;
integrating |u|³≤norm(u)|u|² gives the stated cubic bound. -/
theorem h1_absolute_cube (u : H1) : Integrable (fun x => |H1.rep u x|^3) ∧
    (∫ x, |H1.rep u x|^3)≤‖u‖^3 := by
  -- This rough homogeneous embedding suffices for Riesz; no sharp constant is required here.
  have hb (x : ℝ) : |H1.rep u x|≤‖u‖ := (H1.evaluation_bound u x).trans
    (div_le_self (norm_nonneg _) (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]))
  have hpoint (x : ℝ) : |H1.rep u x|^3≤‖u‖*H1.rep u x^2 := by
    rw [pow_succ,sq_abs,mul_comm]
    exact mul_le_mul_of_nonneg_right (hb x) (sq_nonneg _)
  have hi : Integrable (fun x => |H1.rep u x|^3) := by
    refine ((H1.regular u).value_memLp.integrable_sq.const_mul ‖u‖).mono'
      ((H1.continuous_rep u).abs.pow 3).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hpoint x
  refine ⟨hi,?_⟩
  have hm := integral_mono hi ((H1.regular u).value_memLp.integrable_sq.const_mul ‖u‖)
    hpoint
  rw [integral_const_mul] at hm
  have he := H1.norm_sq_energy u
  have hd : 0≤(∫ x, H1.slope u x^2) := integral_nonneg (fun x => sq_nonneg (H1.slope u x))
  nlinarith [mul_le_mul_of_nonneg_left (show (∫ x, H1.rep u x^2)≤‖u‖^2 by linarith) (norm_nonneg u)]

/-- Every exact H1 representative belongs to L3, including its absolute value.
Use: the Holder products defining the actual finite-energy dual are integrable.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: use the integrable absolute cube and remove the norm with the standard MemLp equivalence. -/
theorem h1_memLp_three (u : H1) : MemLp (H1.rep u) (ENNReal.ofReal 3) volume := by
  have h := memLp_of_power_integrable (H1.continuous_rep u).norm.aestronglyMeasurable
    (fun x => norm_nonneg (H1.rep u x)) (by norm_num : (0:ℝ)<3)
    (by simpa only [Real.norm_eq_abs,Real.rpow_ofNat] using (h1_absolute_cube u).1)
  exact (memLp_norm_iff (H1.continuous_rep u).aestronglyMeasurable).mp h

/-- The actual finite-energy source and any H1 representative have an integrable product.
Use: licenses linearity of the source dual functional and its Riesz pairing.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: finite energy gives L^(3/2), H1 gives L3, and Holder gives L1 for their product. -/
theorem energy_pair_integrable {m : ℝ → ℝ} (hm : Measurable m) (hn : ∀ x, 0≤m x)
    (hE : Integrable (fun x => m x^(3/2 : ℝ))) (u : H1) :
    Integrable (fun x => m x*H1.rep u x) := by
  have hpq : ENNReal.HolderTriple (ENNReal.ofReal (3/2 : ℝ)) (ENNReal.ofReal 3) 1 :=
    ⟨by
      norm_num [ENNReal.ofReal_div_of_pos]
      rw [ENNReal.inv_div (by simp) (by simp),← one_div (3 : ℝ≥0∞),ENNReal.div_add_div_same]
      norm_num
      exact ENNReal.div_self (by norm_num) (by finiteness)⟩
  exact (memLp_of_power_integrable hm.aestronglyMeasurable hn (by norm_num : (0:ℝ)<3/2) hE).integrable_mul
    (h1_memLp_three u)

/-- The actual source dual pairing has a homogeneous H1 norm bound.
Use: constructs a genuine continuous linear functional without an L1 source assumption.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: integral Cauchy--Schwarz in its Holder exponents gives E^(2/3) times
the cube-root absolute-cube norm; the proved H1 cubic bound controls that root. -/
theorem energy_pair_bound {m : ℝ → ℝ} (hm : Measurable m) (hn : ∀ x, 0≤m x)
    (hE : Integrable (fun x => m x^(3/2 : ℝ))) (u : H1) :
    |∫ x, m x*H1.rep u x|≤(∫ x, m x^(3/2 : ℝ))^(2/3 : ℝ)*‖u‖ := by
  -- Only this rough embedding is used for existence; the subsequent sharp proof keeps its exact constants.
  have hmLp := memLp_of_power_integrable hm.aestronglyMeasurable hn (by norm_num : (0:ℝ)<3/2) hE
  have huLp := (h1_memLp_three u).norm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (3/2 : ℝ)) (q := 3) (by norm_num [holderConjugate_iff])
    (Eventually.of_forall hn) (Eventually.of_forall fun x => norm_nonneg (H1.rep u x)) hmLp huLp
  norm_num only [one_div_div,div_one,one_mul,Real.rpow_ofNat,Real.norm_eq_abs] at hh
  have hroot : (∫ x, |H1.rep u x|^3)^(1/3 : ℝ)≤‖u‖ := by
    apply (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg u) (by decide : 3≠0)).mp
    rw [show ((∫ x, |H1.rep u x|^3)^(1/3 : ℝ))^3=(∫ x, |H1.rep u x|^3) by
      simpa only [Nat.cast_one,pow_one] using third_power_cube
        (integral_nonneg (fun x => pow_nonneg (abs_nonneg (H1.rep u x)) 3)) 1]
    exact (h1_absolute_cube u).2
  calc
    _ ≤ ∫ x, |m x*H1.rep u x| := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => m x*H1.rep u x)
    _ = ∫ x, m x*‖H1.rep u x‖ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [abs_mul,abs_of_nonneg (hn x),Real.norm_eq_abs]
    _ ≤ _ := hh.trans (mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg
      (integral_nonneg (fun x => Real.rpow_nonneg (hn x) _)) _))

/-- The actual bounded source functional on the previously constructed exact Sobolev Hilbert space.
Use: Riesz produces the Green potential for the full finite-energy domain.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def energyDual {m : ℝ → ℝ} (hm : Measurable m) (hn : ∀ x, 0≤m x)
    (hE : Integrable (fun x => m x^(3/2 : ℝ))) : StrongDual ℝ H1 :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, m x*H1.rep u x
      map_add' := by
        intro u v
        simp_rw [H1.rep_add,mul_add]
        exact integral_add (energy_pair_integrable hm hn hE u) (energy_pair_integrable hm hn hE v)
      map_smul' := by
        intro c u
        rw [H1.rep_smul]
        change (∫ x, m x*(c*H1.rep u x))=c*(∫ x, m x*H1.rep u x)
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring }
    ((∫ x, m x^(3/2 : ℝ))^(2/3 : ℝ))
    (fun u => by
      change |∫ x, m x*H1.rep u x|≤(∫ x, m x^(3/2 : ℝ))^(2/3 : ℝ)*‖u‖
      exact energy_pair_bound hm hn hE u)

end
end jacobi.Young
