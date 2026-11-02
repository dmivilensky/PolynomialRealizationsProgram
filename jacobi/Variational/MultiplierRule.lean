import jacobi.Variational.DensitySeparation
import jacobi.Variational.NoDescent
import jacobi.Variational.ConeComplementarity
import jacobi.Variational.ConstraintQualification

/-!
Article: jacobi, Lemma D.3.
Actual constrained minimality, a quadratic spectral expansion and strict
dilation imply normal multipliers with positive spectral coefficient and
the pointwise positive-part equation. The proof discharges cone convexity,
descent exclusion, normality, integrability and pointwise complementarity.
The moment applications supply their proved actual gradients and remainders.
Source: the article's cone multiplier argument, using proved Hahn--Banach separation.
Use: its second-moment and top applications prove KKT without assumed multipliers or constraint qualification.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
set_option backward.isDefEq.respectTransparency false

/-- The article's normal pointwise multiplier rule on the full actual finite-energy density domain.
Use: its second-moment and top applications prove KKT without assumed multipliers or constraint qualification.
Article: jacobi, Lemma D.3.
Proof: separate the actual objective, mass and spectral variation image
after excluding strict descent using the genuine energy derivative. Strict
dilation proves normality. The zero density forces the spectral multiplier
positive, and all finite-measure indicator tests give pointwise complementarity. -/
theorem normal_multiplier_rule_local (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) (Φ : Density → ℝ) (γ : ℝ → ℝ)
    (hγm : Measurable γ) {B M T C r k η : ℝ} (hγB : ∀ x,|γ x|≤B)
    (hC : 0<C) (hr : 0<r) (hk : 0<k) (hη : 0<η) (hmM : m.mass≤M) (hmT : T≤Φ m)
    (hmin : ∀ q : Density,q.mass≤M → T≤Φ q → m.energy≤q.energy)
    (hvar : ∀ q : Density,(∫ x,|q.value x-m.value x|)≤r →
      |Φ q-Φ m-(∫ x,γ x*(q.value x-m.value x))|≤C*(∫ x,|q.value x-m.value x|)^2)
    (hgain : ∀ (t : ℝ) (ht : 1≤t),t≤1+η → Φ m+k*(t-1)≤Φ (m.dilate t (by linarith))) :
    ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
      (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (μ*γ x-l) 0 := by
  -- All three tests are integrable on every original density competitor.
  let g : Fin 3 → ℝ → ℝ := ![fun x => (3/2:ℝ)*sqrt (m.value x),fun _ => 1,γ]
  have hγi (q : Density) : Integrable (fun x => γ x*q.value x) :=
    q.integrable.bdd_mul hγm.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hγB x)
  have hi (i : Fin 3) (q : Density) : Integrable (fun x => g i x*q.value x) := by
    fin_cases i
    · convert (objectivePair_integrable m q).const_mul (3/2:ℝ) using 1
      funext x
      change ((3/2:ℝ)*sqrt (m.value x))*q.value x=(3/2:ℝ)*(sqrt (m.value x)*q.value x)
      ring
    · change Integrable (fun x => (1:ℝ)*q.value x)
      simpa only [one_mul] using q.integrable
    · exact hγi q
  have hg0 (q : Density) : densityTest (g 0) q=objectivePair m q := by
    unfold densityTest objectivePair
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change ((3/2:ℝ)*sqrt (m.value x))*q.value x=(3/2:ℝ)*(sqrt (m.value x)*q.value x)
      ring
  have hg1 (q : Density) : densityTest (g 1) q=q.mass := densityTest_one q
  have hc0 (q : Density) : variationCoordinates g m q 0=
      (3/2:ℝ)*(∫ x,sqrt (m.value x)*(q.value x-m.value x)) := by
    rw [variationCoordinates,hg0,hg0,objectivePair_sub]
  have hc1 (q : Density) : variationCoordinates g m q 1=q.mass-m.mass := by
    rw [variationCoordinates,hg1,hg1]
  have hc2 (q : Density) : variationCoordinates g m q 2=∫ x,γ x*(q.value x-m.value x) :=
    densityTest_sub γ m q (hγi m) (hγi q)
  have hno (q : Density) : variationCoordinates g m q∉improvementCone (m.mass=M) := by
    intro h
    apply no_strict_density_descent m q Φ γ hC hr hmM hmT hmin hvar
    refine ⟨?_,?_,?_⟩
    · simpa only [← hc0 q] using h.1
    · intro hactive
      have hh := h.2.1 hactive
      rw [hc1] at hh
      linarith
    · simpa only [← hc2 q] using h.2.2
  have hqual : ∃ q : Density,q.mass=m.mass ∧ 0<variationCoordinates g m q 2 := by
    obtain ⟨q,hqM,hqG⟩ := dilation_constraint_qualification_local m hm hrad Φ
      (fun q => ∫ x,γ x*(q.value x-m.value x)) hC hr hk hη hvar hgain
    exact ⟨q,hqM,by rwa [hc2]⟩
  obtain ⟨l,μ,hl,hμ,hslack,hsep⟩ := density_normal_multipliers (m.mass=M) g hi m hm rfl hno hqual
  have hg0m : densityTest (g 0) m=(3/2:ℝ)*m.energy := by
    rw [hg0,objectivePair]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change sqrt (m.value x)*m.value x=m.value x^(3/2:ℝ)
      rw [rpow_three_halves (m.nonneg x),mul_comm]
  have hμpos : 0<μ := by
    apply lt_of_le_of_ne hμ
    intro hz
    have h := hsep (m.scale 0 le_rfl)
    simp only [variationCoordinates,densityTest_scale,zero_mul,zero_sub] at h
    rw [hg0m,hg1,hz.symm] at h
    nlinarith [m.energy_pos hm]
  -- The separated inequality is now the literal integral of its pointwise coefficient.
  let ψ (x : ℝ) := (3/2:ℝ)*sqrt (m.value x)+l-μ*γ x
  have hψi (q : Density) : Integrable (fun x => ψ x*q.value x) := by
    have h := ((hi 0 q).add (q.integrable.const_mul l)).sub ((hγi q).const_mul μ)
    apply h.congr
    exact Eventually.of_forall fun x => by
      change ((3/2:ℝ)*sqrt (m.value x))*q.value x+l*q.value x-μ*(γ x*q.value x)=ψ x*q.value x
      dsimp only [ψ]
      ring
  have hψtest (q : Density) : densityTest ψ q=
      densityTest (g 0) q+l*q.mass-μ*densityTest γ q := by
    have he : (fun x => ψ x*q.value x)=
        ((fun x => g 0 x*q.value x)+(fun x => l*q.value x))-(fun x => μ*(γ x*q.value x)) := by
      funext x
      change ψ x*q.value x=((3/2:ℝ)*sqrt (m.value x))*q.value x+l*q.value x-μ*(γ x*q.value x)
      dsimp only [ψ]
      ring
    unfold densityTest
    rw [he,integral_sub' ((hi 0 q).add (q.integrable.const_mul _)) ((hγi q).const_mul _),
      integral_add' (hi 0 q) (q.integrable.const_mul _),integral_const_mul,integral_const_mul]
    rfl
  have hψvar (q : Density) : 0≤∫ x,ψ x*(q.value x-m.value x) := by
    rw [← densityTest_sub ψ m q (hψi m) (hψi q),hψtest q,hψtest m]
    have h := hsep q
    simp only [variationCoordinates,hg1] at h
    change 0≤densityTest (g 0) q-densityTest (g 0) m+l*(q.mass-m.mass)-
      μ*(densityTest γ q-densityTest γ m) at h
    linarith
  obtain ⟨hψ,hψm⟩ := density_cone_complementarity m ψ hψi hψvar
  refine ⟨μ,l,hμpos,hl,?_,positivePart_of_complementarity m γ μ l hψ hψm⟩
  by_cases hactive : m.mass=M
  · rw [hactive,sub_self,mul_zero]
  · rw [hslack hactive,zero_mul]

/-- The actual normal multiplier rule on the moment dilation interval [1,2].
Use: the G_2 and top-eigenvalue applications share their existing uniform dilation interval.
Article: jacobi, Lemma D.3.
Proof: specialize the proved local multiplier theorem to eta=1. -/
theorem normal_multiplier_rule (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) (Φ : Density → ℝ) (γ : ℝ → ℝ)
    (hγm : Measurable γ) {B M T C r k : ℝ} (hγB : ∀ x,|γ x|≤B)
    (hC : 0<C) (hr : 0<r) (hk : 0<k) (hmM : m.mass≤M) (hmT : T≤Φ m)
    (hmin : ∀ q : Density,q.mass≤M → T≤Φ q → m.energy≤q.energy)
    (hvar : ∀ q : Density,(∫ x,|q.value x-m.value x|)≤r →
      |Φ q-Φ m-(∫ x,γ x*(q.value x-m.value x))|≤C*(∫ x,|q.value x-m.value x|)^2)
    (hgain : ∀ (t : ℝ) (ht : 1≤t),t≤2 → Φ m+k*(t-1)≤Φ (m.dilate t (by linarith))) :
    ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
      (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (μ*γ x-l) 0 :=
  normal_multiplier_rule_local m hm hrad Φ γ hγm hγB hC hr hk zero_lt_one hmM hmT hmin hvar
    (by simpa only [one_add_one_eq_two] using hgain)

end
end jacobi.Variational
