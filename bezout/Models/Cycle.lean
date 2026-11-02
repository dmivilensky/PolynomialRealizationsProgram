import bezout.Models.Network
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
Article: bezout, active cycle modes in the two-network model.
Use: the actual finite cyclic Laplacian has the claimed cosine eigenvalues;
its modes lift to the coupled disagreement Hessian without a numerical eigensolver.
Proof: cyclic additive characters diagonalize nearest-neighbor shifts;
taking real parts gives nonzero real cosine modes.
-/

namespace bezout.Models.Network
noncomputable section
open Complex
variable (m : ℕ) [NeZero m]

/-- The literal nearest-neighbor Laplacian on a finite cycle. -/
def cycleLaplacian : (ZMod m → ℝ) →ₗ[ℝ] (ZMod m → ℝ) where
  toFun u i := 2*u i-u (i+1)-u (i-1)
  map_add' u v := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c u := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The j-th real cyclic mode, including its nonzero value at vertex zero. -/
def cycleMode (j : ZMod m) (i : ZMod m) : ℝ := (ZMod.stdAddChar (j*i)).re

/-- The exact Laplacian eigenvalue in the article's active spectral list. -/
def cycleEigenvalue (j : ZMod m) : ℝ := 2-2*Real.cos (2*Real.pi*(j.val:ℝ)/m)

/-- The real part of the cyclic character is the displayed cosine. -/
theorem character_real (j : ZMod m) :
    (ZMod.stdAddChar j).re=Real.cos (2*Real.pi*(j.val:ℝ)/m) := by
  have h := ZMod.stdAddChar_coe (N := m) (j.val:ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at h
  rw [h]
  simp only [Complex.exp_re, Complex.div_re, Complex.div_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, add_zero, zero_add, sub_zero, zero_sub, mul_one]
  norm_num
  congr 1
  field_simp

/-- Negative cyclic frequencies are complex conjugates of the positive ones. -/
theorem character_neg (j : ZMod m) : ZMod.stdAddChar (-j)=star (ZMod.stdAddChar j) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact Circle.coe_inv_eq_conj _

/-- Actual nearest-neighbor action gives every claimed real cosine eigenmode. -/
theorem cycle_mode_eigenvector (j : ZMod m) :
    cycleLaplacian m (cycleMode m j)=cycleEigenvalue m j • cycleMode m j := by
  funext i
  have hplus : j*(i+1)=j*i+j := by ring
  have hminus : j*(i-1)=j*i+(-j) := by ring
  change 2*(ZMod.stdAddChar (j*i)).re-(ZMod.stdAddChar (j*(i+1))).re-
    (ZMod.stdAddChar (j*(i-1))).re=cycleEigenvalue m j*(ZMod.stdAddChar (j*i)).re
  simp only [hplus, hminus, AddChar.map_add_eq_mul, character_neg, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, cycleEigenvalue]
  rw [← character_real m j]
  ring

/-- Every displayed real eigenmode is nonzero, even at repeated eigenvalues. -/
theorem cycleMode_ne_zero (j : ZMod m) : cycleMode m j≠0 := by
  intro hz
  have h := congrFun hz 0
  simp [cycleMode] at h

omit [NeZero m] in
/-- All active cycle eigenvalues lie in the exact interval [0,4]. -/
theorem cycleEigenvalue_mem (j : ZMod m) : cycleEigenvalue m j ∈ Set.Icc (0:ℝ) 4 := by
  unfold cycleEigenvalue
  constructor <;> linarith [Real.neg_one_le_cos (2*Real.pi*(j.val:ℝ)/m),
    Real.cos_le_one (2*Real.pi*(j.val:ℝ)/m)]

omit [NeZero m] in
/-- The constant disagreement mode realizes the lower Laplacian endpoint. -/
@[simp] theorem cycleEigenvalue_zero : cycleEigenvalue m 0=0 := by
  simp [cycleEigenvalue]

/-- For every nonzero even cycle the alternating mode attains the upper endpoint four. -/
theorem cycleEigenvalue_half (hm : Even m) :
    cycleEigenvalue m ((m/2:ℕ):ZMod m)=4 := by
  have hmpos : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hhalf : m/2<m := Nat.div_lt_self hmpos (by norm_num)
  have hmul : m/2*2=m := Nat.div_mul_cancel hm.two_dvd
  have hcast : ((m/2:ℕ):ℝ)*2=(m:ℝ) := by exact_mod_cast hmul
  have hmreal : (m:ℝ)≠0 := by exact_mod_cast NeZero.ne m
  unfold cycleEigenvalue
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hhalf]
  have ha : 2*Real.pi*((m/2:ℕ):ℝ)/(m:ℝ)=Real.pi := by
    apply (div_eq_iff hmreal).mpr
    calc
      2*Real.pi*((m/2:ℕ):ℝ)=Real.pi*(((m/2:ℕ):ℝ)*2) := by ring
      _=Real.pi*(m:ℝ) := by rw [hcast]
  rw [ha, Real.cos_pi]
  norm_num

/-- Every real cyclic mode lifts to the coupled network's claimed active eigenvalue. -/
theorem coupled_cycle_mode (j : ZMod m) (a : ℝ) :
    hessian (cycleLaplacian m) a (antisymmetric (cycleMode m j))=
      ((cycleEigenvalue m j+2*a)/(4+2*a)) • antisymmetric (cycleMode m j) :=
  eigenmode _ a _ _ (cycle_mode_eigenvector m j)

end
end bezout.Models.Network
