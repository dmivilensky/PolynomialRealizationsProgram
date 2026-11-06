import nesterov.Attainment.LagPolynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.RingTheory.Coprime.Lemmas

/-! A nonpositive real trigonometric symbol has double roots at its interior
zero angles. Conjugate symmetry then gives the sharp half-degree atom bound. -/
noncomputable section
open Polynomial Set Filter
open scoped Topology BigOperators
namespace nesterov.Attainment

theorem finite_double_roots_card_le (P : Polynomial ℂ) (hP : P ≠ 0) (S : Finset ℂ)
    (hroot : ∀ z∈S, P.IsRoot z ∧ P.derivative.IsRoot z) : 2*S.card ≤ P.natDegree := by
  classical
  have hdiv (z : ℂ) (hz : z∈S) : (X-C z)^2 ∣ P :=
    (le_rootMultiplicity_iff hP).mp (by
      have hh := (one_lt_rootMultiplicity_iff_isRoot hP).mpr (hroot z hz)
      omega)
  have hprod : (∏ z∈S,(X-C z)^2) ∣ P := Finset.prod_dvd_of_coprime
    (by intro x _ y _ hxy; exact (pairwise_coprime_X_sub_C Function.injective_id hxy).pow) hdiv
  have hdeg : (∏ z∈S,(X-C z)^2 : Polynomial ℂ).natDegree=2*S.card := by
    rw [natDegree_prod S (fun z : ℂ => (X-C z)^2) (fun z _ => pow_ne_zero _ (X_sub_C_ne_zero z))]
    simp [natDegree_pow,Nat.mul_comm]
  rw [← hdeg]
  exact natDegree_le_of_dvd hprod hP

theorem hasDerivAt_unitPhase (ω : ℝ) :
    HasDerivAt (fun x : ℝ => polyak.Waves.z 0 x) (polyak.Waves.z 0 ω*Complex.I) ω := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := ω)).mul_const Complex.I |>.cexp
  simpa only [polyak.Waves.z,Complex.ofRealCLM_apply,Complex.ofReal_one,Complex.ofReal_zero,zero_add,one_mul] using h

set_option backward.isDefEq.respectTransparency false in
/-- Fermat's theorem gives a double polynomial root at every interior zero
of a nonpositive real symbol represented on the unit circle. -/
theorem curve_double_root (P : Polynomial ℝ) (K : ℕ) (φ : ℝ → ℝ)
    (heq : ∀ ω,ceval P (polyak.Waves.z 0 ω)=polyak.Waves.z 0 ω^K*(φ ω : ℂ))
    (hneg : ∀ ω∈Ioo (0:ℝ) Real.pi, φ ω ≤ 0) {ω : ℝ}
    (hω : ω∈Ioo (0:ℝ) Real.pi) (hφ : DifferentiableAt ℝ φ ω) (hzero : φ ω=0) :
    ceval P (polyak.Waves.z 0 ω)=0 ∧ ceval P.derivative (polyak.Waves.z 0 ω)=0 := by
  have hmax : IsLocalMax φ ω := by
    filter_upwards [Ioo_mem_nhds hω.1 hω.2] with x hx
    rw [hzero]
    exact hneg x hx
  have hφ' : HasDerivAt φ 0 ω := by
    have hh := hφ.hasDerivAt
    rwa [hmax.deriv_eq_zero] at hh
  have hR := ((hasDerivAt_unitPhase ω).pow K).mul hφ'.ofReal_comp
  have hR0 : HasDerivAt (fun x : ℝ => polyak.Waves.z 0 x^K*(φ x : ℂ)) 0 ω := by
    simpa only [Pi.pow_apply,Pi.mul_apply,hzero,Complex.ofReal_zero,mul_zero,zero_mul,add_zero] using! hR
  have hfun : (fun x : ℝ => ceval P (polyak.Waves.z 0 x))=
      (fun x : ℝ => polyak.Waves.z 0 x^K*(φ x : ℂ)) := funext heq
  rw [← hfun] at hR0
  have hP' := ((P.map Complex.ofRealHom).hasDerivAt (polyak.Waves.z 0 ω)).comp ω
    (hasDerivAt_unitPhase ω)
  have he := hP'.unique hR0
  have hd := (mul_eq_zero.mp he).resolve_right
    (mul_ne_zero (polyak.Waves.z_ne_zero 0 ω) Complex.I_ne_zero)
  refine ⟨by rw [heq,hzero,Complex.ofReal_zero,mul_zero],?_⟩
  simpa only [ceval,Polynomial.derivative_map] using hd

def frequencyPhase (c : nesterov.Spectral.Frequency) : ℂ := polyak.Waves.z 0 (Real.arccos c)

theorem frequencyPhase_re (c : nesterov.Spectral.Frequency) : (frequencyPhase c).re=c := by
  simpa only [frequencyPhase,pow_one,Nat.cast_one,one_mul,mul_zero,Real.exp_zero,
    Real.cos_arccos c.property.1 c.property.2] using polyak.Waves.z_pow_re 0 (Real.arccos c) 1

theorem frequencyPhase_injective : Function.Injective frequencyPhase := by
  intro c c' he
  apply Subtype.ext
  simpa only [frequencyPhase_re] using congrArg Complex.re he

theorem frequencyPhase_im_pos {c : nesterov.Spectral.Frequency}
    (hc : -1 < (c:ℝ) ∧ (c:ℝ) < 1) : 0 < (frequencyPhase c).im := by
  have he : (frequencyPhase c).im=Real.sin (Real.arccos c) := by
    simpa only [frequencyPhase,pow_one,Nat.cast_one,one_mul,mul_zero,Real.exp_zero] using
      polyak.Waves.z_pow_im 0 (Real.arccos c) 1
  rw [he]
  exact Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hc.2) (Real.arccos_lt_pi.mpr hc.1)

/-- Both the zero and its conjugate are double roots of the real polynomial. -/
theorem half_circle_double_roots_card_le (P : Polynomial ℝ) (hP : P ≠ 0)
    (F : Finset nesterov.Spectral.Frequency)
    (hFi : ∀ c∈F,-1 < (c:ℝ) ∧ (c:ℝ) < 1)
    (hr : ∀ c∈F,ceval P (frequencyPhase c)=0 ∧ ceval P.derivative (frequencyPhase c)=0) :
    4*F.card ≤ P.natDegree := by
  classical
  let S := F.image frequencyPhase
  let T := S.image star
  have hpos : ∀ z∈S,0 < z.im := by
    intro z hz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
    exact frequencyPhase_im_pos (hFi c hc)
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro z hz hzt
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hzt
    have hp := hpos w hw
    have hn := hpos (star w) hz
    simp only [Complex.star_def,Complex.conj_im] at hn
    linarith
  have hS : S.card=F.card := Finset.card_image_of_injective _ frequencyPhase_injective
  have hT : T.card=S.card := Finset.card_image_of_injective _ star_injective
  have hmap : P.map Complex.ofRealHom ≠ 0 := by
    exact Polynomial.map_ne_zero hP
  have hroot : ∀ z∈S∪T, (P.map Complex.ofRealHom).IsRoot z ∧
      (P.map Complex.ofRealHom).derivative.IsRoot z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨(hr c hc).1,by
        rw [Polynomial.derivative_map]
        exact (hr c hc).2⟩
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hw
      constructor
      · change ceval P (star (frequencyPhase c))=0
        rw [ceval_conj,(hr c hc).1,star_zero]
      · change ((P.map Complex.ofRealHom).derivative).eval (star (frequencyPhase c))=0
        rw [Polynomial.derivative_map]
        change ceval P.derivative (star (frequencyPhase c))=0
        rw [ceval_conj,(hr c hc).2,star_zero]
  have hh := finite_double_roots_card_le (P.map Complex.ofRealHom) hmap (S∪T) hroot
  simp only [Finset.card_union_of_disjoint hdis,hT,hS] at hh
  exact (by omega : 4*F.card ≤ (P.map Complex.ofRealHom).natDegree).trans Polynomial.natDegree_map_le

end nesterov.Attainment
