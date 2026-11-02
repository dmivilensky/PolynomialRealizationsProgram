import jacobi.Variational.DensityCone
import jacobi.Variational.ConeSeparation

/-!
Article: jacobi, Lemma D.3.
Three integrable linear tests of finite-energy densities have a convex
variation image. Its separation yields Fritz John coefficients for every
actual density competitor, and a proved mass-preserving positive spectral
direction excludes the abnormal zero objective coefficient. The remaining
variational application supplies exclusion of descent directions from actual
minimality, rather than assuming multiplier equations.
Source: convex segments of the density domain and finite-dimensional Hahn--Banach separation.
Use: the multiplier image uses the objective gradient, the constant mass test, and the spectral gradient.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set
set_option backward.isDefEq.respectTransparency false

/-- A finite linear test of an actual density.
Use: the multiplier image uses the objective gradient, the constant mass test, and the spectral gradient.
Article: jacobi, Lemma D.3.
-/
def densityTest (g : ℝ → ℝ) (m : Density) : ℝ := ∫ x,g x*m.value x

/-- Three actual linear test differences at the base density.
Use: the finite-dimensional object separated from the strict-improvement cone.
Article: jacobi, Lemma D.3.
-/
def variationCoordinates (g : Fin 3 → ℝ → ℝ) (m q : Density) (i : Fin 3) : ℝ :=
  densityTest (g i) q-densityTest (g i) m

/-- The actual finite-dimensional variation image of the full density domain.
Use: permits Hahn--Banach separation without selecting finitely many density variations.
Article: jacobi, Lemma D.3.
-/
def variationImage (g : Fin 3 → ℝ → ℝ) (m : Density) : Set (Fin 3 → ℝ) :=
  Set.range (variationCoordinates g m)

/-- Every actual linear-test variation image is convex and contains zero.
Use: all hypotheses about the separated set follow from the original density cone.
Article: jacobi, Lemma D.3.
Proof: the density segment realizes each convex combination of the three
linear test differences simultaneously, and the base density gives zero. -/
theorem variationImage_convex (g : Fin 3 → ℝ → ℝ)
    (hi : ∀ i (q : Density),Integrable (fun x => g i x*q.value x)) (m : Density) :
    Convex ℝ (variationImage g m) ∧ 0∈variationImage g m := by
  -- All coordinates are realized by one common actual density segment.
  constructor
  · intro x hx y hy a b ha hb hab
    obtain ⟨q,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    refine ⟨q.segment v b hb (by linarith),?_⟩
    funext i
    change (∫ x,g i x*(q.segment v b hb (by linarith)).value x)-densityTest (g i) m=
      a*(densityTest (g i) q-densityTest (g i) m)+b*(densityTest (g i) v-densityTest (g i) m)
    rw [densityTest_segment (g i) q v (hi i q) (hi i v)]
    change (1-b)*densityTest (g i) q+b*densityTest (g i) v-densityTest (g i) m=_
    have haeq : a=1-b := by linarith
    rw [haeq]
    ring
  · refine ⟨m,?_⟩
    funext i
    exact sub_self _

/-- Exclusion of actual strict descent variations yields Fritz John coefficients on every density competitor.
Use: transfers the finite-dimensional separation theorem back to the article's complete density domain.
Article: jacobi, Lemma D.3.
Proof: the actual variation image is convex and contains zero. The given
descent exclusion makes it disjoint from the strict-improvement cone, so
the proved separation theorem applies directly. -/
theorem density_fritzJohn (active : Prop) (g : Fin 3 → ℝ → ℝ)
    (hi : ∀ i (q : Density),Integrable (fun x => g i x*q.value x)) (m : Density)
    (hno : ∀ q : Density,variationCoordinates g m q∉improvementCone active) :
    ∃ a l μ : ℝ,0≤a ∧ 0≤l ∧ 0≤μ ∧ (a≠0 ∨ l≠0 ∨ μ≠0) ∧
      (¬active → l=0) ∧ ∀ q : Density,
        0≤a*variationCoordinates g m q 0+l*variationCoordinates g m q 1-
          μ*variationCoordinates g m q 2 := by
  -- Separation is applied to the full image, not to an unproved limiting family of tests.
  obtain ⟨hc,hzero⟩ := variationImage_convex g hi m
  have hdis : Disjoint (improvementCone active) (variationImage g m) := by
    apply Set.disjoint_left.mpr
    intro v hv hvr
    obtain ⟨q,rfl⟩ := hvr
    exact hno q hv
  obtain ⟨a,l,μ,ha,hl,hμ,hn,hslack,hsep⟩ := variation_fritzJohn active hc hzero hdis
  exact ⟨a,l,μ,ha,hl,hμ,hn,hslack,fun q => hsep _ ⟨q,rfl⟩⟩

/-- A constant mass test reads the actual density mass, including every competitor.
Use: identifies the separated mass coordinate with the original linear constraint.
Article: jacobi, Lemma D.3.
Proof: multiplication by one leaves the actual mass integrand unchanged. -/
theorem densityTest_one (m : Density) : densityTest (fun _ => 1) m=m.mass := by
  simp only [densityTest,one_mul,Density.mass]

/-- Every linear density test is exactly homogeneous under nonnegative amplitude scaling.
Use: the zero density tests all separated coefficients simultaneously in the normality proof.
Article: jacobi, Lemma D.3.
Proof: factor the actual scalar amplitude out of the Lebesgue integral. -/
theorem densityTest_scale (g : ℝ → ℝ) (m : Density) (c : ℝ) (hc : 0≤c) :
    densityTest g (m.scale c hc)=c*densityTest g m := by
  unfold densityTest
  change (∫ x,g x*(c*m.value x))=_
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only; ring

/-- Differences of integrable density tests equal the test of the actual signed density difference.
Use: identifies the separated spectral coordinate with the gradient integral in the quadratic expansion.
Article: jacobi, Lemma D.3.
Proof: distribute the pointwise product and use the integrable subtraction theorem. -/
theorem densityTest_sub (g : ℝ → ℝ) (m q : Density)
    (hm : Integrable (fun x => g x*m.value x)) (hq : Integrable (fun x => g x*q.value x)) :
    densityTest g q-densityTest g m=∫ x,g x*(q.value x-m.value x) := by
  unfold densityTest
  rw [← integral_sub hq hm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only; ring

/-- Proved constraint qualification normalizes the actual separated objective coefficient.
Use: produces genuine KKT coefficients from the full density variation image; their existence is not assumed.
Article: jacobi, Lemma D.3.
Proof: a mass-preserving direction with positive linear spectral variation
would force mu=0 if a=0. The zero competitor and the positive mass test then
force lambda=0, contradicting the proved nontriviality of separation. -/
theorem density_normal_multipliers (active : Prop) (g : Fin 3 → ℝ → ℝ)
    (hi : ∀ i (q : Density),Integrable (fun x => g i x*q.value x)) (m : Density)
    (hm : 0<m.mass) (hg1 : g 1=fun _ => 1)
    (hno : ∀ q : Density,variationCoordinates g m q∉improvementCone active)
    (hqual : ∃ q : Density,q.mass=m.mass ∧ 0<variationCoordinates g m q 2) :
    ∃ l μ : ℝ,0≤l ∧ 0≤μ ∧ (¬active → l=0) ∧ ∀ q : Density,
      0≤variationCoordinates g m q 0+l*variationCoordinates g m q 1-
        μ*variationCoordinates g m q 2 := by
  -- Positivity of the objective coefficient is deduced from an actual qualified density direction.
  obtain ⟨a,l,μ,ha,hl,hμ,hn,hslack,hsep⟩ := density_fritzJohn active g hi m hno
  have hg1q (q : Density) : variationCoordinates g m q 1=q.mass-m.mass := by
    simp only [variationCoordinates,hg1,densityTest_one]
  have hap : 0<a := by
    by_contra! hzero
    have haz : a=0 := le_antisymm hzero ha
    obtain ⟨q,hqM,hqG⟩ := hqual
    have hq := hsep q
    rw [haz,hg1q,hqM,sub_self,mul_zero,zero_mul,zero_add] at hq
    have hμz : μ=0 := by nlinarith
    have hz := hsep (m.scale 0 le_rfl)
    rw [haz,hμz,zero_mul,zero_mul,zero_add,sub_zero,hg1q,Density.scale_mass,zero_mul] at hz
    have hlz : l=0 := by nlinarith
    exact hn.elim (fun h => h haz) (fun h => h.elim (fun h => h hlz) (fun h => h hμz))
  refine ⟨l/a,μ/a,div_nonneg hl ha,div_nonneg hμ ha,?_,?_⟩
  · intro h
    rw [hslack h,zero_div]
  · intro q
    have h := div_nonneg (hsep q) hap.le
    convert h using 1
    field_simp

end
end jacobi.Variational
