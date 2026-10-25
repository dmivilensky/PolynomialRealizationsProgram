import polyak.ModeLocking.TwoLag.HermiteConstruction
import polyak.Numerics.Parametric.DyadicCheck
import polyak.Numerics.Parametric.Bounds

/-! The exact 3/13 example: denominator-cleared Hermite compatibility source.
The data archive supplies only rational proposals; these definitions fix the equations. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag LeanCert.Core LeanCert.Engine

def u : ℝ := 6*Real.pi/13
def v : ℝ := 4*Real.pi/13
def c₁ : ℝ := Real.cos u
def c₂ : ℝ := Real.cos v

def numerator (r c : ℝ) : ℝ := (1+c)*(1-r*(8*c^3-4*c))
def denominator (r c : ℝ) : ℝ := 1+8*r*c^2*(1+c)
def numeratorD (r c : ℝ) : ℝ := 1-r*(32*c^3+24*c^2-8*c-4)
def denominatorD (r c : ℝ) : ℝ := 8*r*c*(2+3*c)
def derivativeNumerator (r c : ℝ) : ℝ :=
  numeratorD r c*denominator r c-numerator r c*denominatorD r c

def compatibility (r : ℝ) : ℝ :=
  (c₁-c₂)*(derivativeNumerator r c₁*(denominator r c₂)^2+
    derivativeNumerator r c₂*(denominator r c₁)^2)-
      2*(numerator r c₁*denominator r c₂-numerator r c₂*denominator r c₁)*
        denominator r c₁*denominator r c₂

theorem W_four (c : ℝ) : W 4 c=8*c^2*(1+c) := by
  by_cases hc : c=1
  · subst c; norm_num [W_one]
  · rw [W_quotient 4 hc]
    unfold Spectral.chebT
    have h3 := Polynomial.Chebyshev.T_add_two ℝ 1
    have h4 := Polynomial.Chebyshev.T_add_two ℝ 2
    norm_num at h3 h4
    norm_num only [Nat.cast_ofNat]
    rw [h4,h3]
    norm_num [Polynomial.Chebyshev.T_two,Polynomial.Chebyshev.T_one]
    field_simp
    ring

theorem U_three (c : ℝ) : Spectral.chebU 3 c=8*c^3-4*c := by
  unfold Spectral.chebU
  have h := Polynomial.Chebyshev.U_add_two ℝ 1
  norm_num at h
  norm_num only [Nat.cast_ofNat]
  rw [h]
  norm_num [Polynomial.Chebyshev.U_two,Polynomial.Chebyshev.U_one]
  ring

theorem psi_four (r c : ℝ) : Psi 4 r c=numerator r c/denominator r c := by
  change (1+c)*(1-r*Spectral.chebU 3 c)/(1+r*W 4 c)=_
  rw [W_four,U_three]
  dsimp [numerator,denominator]
  congr 1
  ring

theorem denominator_pos {r c : ℝ} (hr : 0≤r) (hc : c∈Set.Icc (-1 : ℝ) 1) :
    0<denominator r c := by
  have h := Psi_den_pos 4 hr hc
  simpa only [W_four,denominator,mul_assoc,mul_left_comm,mul_comm] using h

theorem numerator_hasDerivAt (r c : ℝ) : HasDerivAt (numerator r) (numeratorD r c) c := by
  have hp : HasDerivAt (fun z : ℝ=>8*z^3-4*z) (24*c^2-4) c := by
    convert (((hasDerivAt_id c).pow 3).const_mul 8).sub
      ((hasDerivAt_id c).const_mul 4) using 1
    · ext z
      simp
    · simp
      ring
  have hn := ((hasDerivAt_const c 1).sub (hp.const_mul r))
  have h := ((hasDerivAt_id c).const_add 1).mul hn
  convert h using 1
  · ext z
    simp [numerator]
  · simp only [id_eq]
    dsimp [numeratorD]
    ring

theorem denominator_hasDerivAt (r c : ℝ) : HasDerivAt (denominator r) (denominatorD r c) c := by
  have h := ((((hasDerivAt_id c).pow 2).const_mul (8*r)).mul
    ((hasDerivAt_id c).const_add 1)).const_add 1
  convert h using 1
  · ext z
    simp [denominator]
  · simp only [id_eq,Pi.pow_apply]
    dsimp [denominatorD]
    ring

theorem psi_four_deriv {r c : ℝ} (h : denominator r c≠0) :
    deriv (Psi 4 r) c=derivativeNumerator r c/(denominator r c)^2 := by
  have he : Psi 4 r=(fun c=>numerator r c/denominator r c) := funext (psi_four r)
  rw [he]
  exact ((numerator_hasDerivAt r c).div (denominator_hasDerivAt r c) h).deriv

theorem c₁_mem : c₁∈Set.Ioo (-1 : ℝ) 1 :=
  cos_mem_open (by constructor <;> dsimp [u] <;> linarith [Real.pi_pos])
theorem c₂_mem : c₂∈Set.Ioo (-1 : ℝ) 1 :=
  cos_mem_open (by constructor <;> dsimp [v] <;> linarith [Real.pi_pos])
theorem c₁_lt_c₂ : c₁<c₂ := by
  apply Real.strictAntiOn_cos (by constructor <;> dsimp [v] <;> linarith [Real.pi_pos])
    (by constructor <;> dsimp [u] <;> linarith [Real.pi_pos])
  dsimp [u,v]
  linarith [Real.pi_pos]

theorem compatibility_eq_zero_iff {r : ℝ} (hr : 0≤r) :
    compatibility r=0 ↔ G 4 r c₁ c₂=0 := by
  have h₁ := (denominator_pos hr ⟨c₁_mem.1.le,c₁_mem.2.le⟩).ne'
  have h₂ := (denominator_pos hr ⟨c₂_mem.1.le,c₂_mem.2.le⟩).ne'
  have hc := sub_ne_zero.mpr c₁_lt_c₂.ne
  unfold G
  rw [psi_four_deriv h₁,psi_four_deriv h₂,psi_four,psi_four]
  dsimp [compatibility]
  field_simp
  constructor <;> intro h <;> linear_combination h

end polyak.CertifiedExamples.Exact313
