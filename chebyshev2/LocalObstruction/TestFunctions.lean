import chebyshev2.LocalObstruction.CompactPerturbation
import chebyshev2.LocalObstruction.Annihilator
import chebyshev2.LocalObstruction.SineDecay

/-!
Article: chebyshev2, Theorem 6.1.
The two independent normalization directions in Theorem 6.1.
Use: `chebyshev2.LocalObstruction.sine_normalization_directions` feeds
`chebyshev2.LocalObstruction.sine_nonstationary_test` (sine nonstationary test).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/--
Constructs `smoothTests` of type `Submodule ℝ (ℝ → ℝ)` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.LocalObstruction.SmoothTest` uses this definition in the displayed
construction of `SmoothTest`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def smoothTests : Submodule ℝ (ℝ → ℝ) where
  carrier := {v | ContDiff ℝ ∞ v ∧ HasCompactSupport v}
  zero_mem' := ⟨contDiff_const,HasCompactSupport.zero⟩
  add_mem' := fun hv hw => ⟨hv.1.add hw.1,hv.2.add hw.2⟩
  smul_mem' := fun c v hv => ⟨hv.1.const_smul c,by
    change HasCompactSupport (fun x => c*v x)
    exact hv.2.mul_left⟩

/--
Defines `SmoothTest` of type `` by `smoothTests`.

Use: `chebyshev2.LocalObstruction.unit_mass_test_exists` uses this definition to establish
constructs witnesses with the exact properties `∃ v : SmoothTest, testIntegral (fun _ => 1)
continuous_const v=1`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
abbrev SmoothTest := smoothTests

/--
Supplies the typeclass structure specified by `CoeFun SmoothTest (fun _ => ℝ → ℝ)`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Theorem 6.1.
-/
instance : CoeFun SmoothTest (fun _ => ℝ → ℝ) := ⟨fun v => v.val⟩

/--
Integrability of the displayed function: `Integrable (fun x => v x*g x)`.

Use: `chebyshev2.LocalObstruction.independent_normalization_directions` rewrites with this
integrability result to construct witnesses satisfying `∃ w₀ w₁ :
SmoothTest, testIntegral (fun _ => 1) continuous_const w₀=1 ∧ testIntegral (fun _ => 1)
continuous_const w₁=1 ∧ testIntegral g hg w₀≠testIntegral g hg w₁`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem test_integrable (v : SmoothTest) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun x => v x*g x) :=
  (v.property.1.continuous.mul hg).integrable_of_hasCompactSupport v.property.2.mul_right

/--
Constructs `testIntegral` of type `SmoothTest →ₗ[ℝ] ℝ` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.LocalObstruction.independent_normalization_directions` uses this
definition to construct witnesses satisfying `∃ w₀ w₁ : SmoothTest, testIntegral (fun _ => 1)
continuous_const w₀=1 ∧ testIntegral (fun _ => 1) continuous_const w₁=1 ∧ testIntegral g hg
w₀≠testIntegral g hg w₁`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def testIntegral (g : ℝ → ℝ) (hg : Continuous g) : SmoothTest →ₗ[ℝ] ℝ where
  toFun v := ∫ x, v x*g x
  map_add' := by
    intro v w
    change (∫ x, (v x+w x)*g x)=(∫ x, v x*g x)+(∫ x, w x*g x)
    simp only [add_mul]
    exact integral_add (test_integrable v hg) (test_integrable w hg)
  map_smul' := by
    intro c v
    change (∫ x, (c*v x)*g x)=c*(∫ x, v x*g x)
    simp only [mul_assoc,integral_const_mul]

/--
Constructs witnesses with the exact properties `∃ v : SmoothTest, testIntegral (fun _ => 1)
continuous_const v=1`.

Use: `chebyshev2.LocalObstruction.independent_normalization_directions` uses this identity
to construct witnesses satisfying `∃ w₀ w₁ : SmoothTest, testIntegral
(fun _ => 1) continuous_const w₀=1 ∧ testIntegral (fun _ => 1) continuous_const w₁=1 ∧
testIntegral g hg w₀≠testIntegral g hg w₁`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem unit_mass_test_exists : ∃ v : SmoothTest, testIntegral (fun _ => 1) continuous_const v=1 := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  have hex : ∃ v : SmoothTest, testIntegral (fun _ => 1) continuous_const v ≠ 0 := by
    by_contra h
    push Not at h
    have hf : (fun _ : ℝ => (1:ℝ))=0 := continuous_eq_zero_of_test_integrals continuous_const
      (fun v hv hc => by exact h ⟨v,hv,hc⟩)
    have := congrFun hf 0
    norm_num at this
  obtain ⟨v,hv⟩ := hex
  refine ⟨(testIntegral (fun _ => 1) continuous_const v)⁻¹ • v,?_⟩
  simp only [map_smul,smul_eq_mul,inv_mul_cancel₀ hv]

/--
Constructs witnesses with the exact properties `∃ w₀ w₁ : SmoothTest, testIntegral (fun _ => 1)
continuous_const w₀=1 ∧ testIntegral (fun _ => 1) continuous_const w₁=1 ∧ testIntegral g hg
w₀≠testIntegral g hg w₁`.

Use: `chebyshev2.LocalObstruction.sine_normalization_directions` uses this identity to
establish constructs witnesses with the exact properties `∃ w₀ w₁ : SmoothTest, (∫ x, w₀ x)=1 ∧
(∫ x, w₁ x)=1 ∧ (∫ x, w₀ x/(2*chebyshev2.SineContinuum.n x))≠ (∫ x, w₁
x/(2*chebyshev2.SineContinuum.n x))`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem independent_normalization_directions {g : ℝ → ℝ} (hg : Continuous g)
    (hne : ∃ a b, g a≠g b) :
    ∃ w₀ w₁ : SmoothTest,
      testIntegral (fun _ => 1) continuous_const w₀=1 ∧
      testIntegral (fun _ => 1) continuous_const w₁=1 ∧
      testIntegral g hg w₀≠testIntegral g hg w₁ := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  let m₀ := testIntegral (fun _ => 1) continuous_const
  let m₁ := testIntegral g hg
  obtain ⟨w₀,hw₀⟩ := unit_mass_test_exists
  have hz : ∃ z : SmoothTest, m₀ z=0 ∧ m₁ z≠0 := by
    by_contra h
    have hker : ∀ z : SmoothTest, m₀ z=0 → m₁ z=0 := by
      intro z hz
      by_contra hne
      exact h ⟨z,hz,hne⟩
    have hall (v : SmoothTest) : m₁ v=(m₁ w₀)*m₀ v := by
      have h₀ : m₀ w₀=1 := hw₀
      have hi := hker (v-(m₀ v) • w₀) (by simp [h₀])
      simp only [map_sub,map_smul,smul_eq_mul] at hi
      linarith
    have hzero : (fun x => g x-m₁ w₀)=0 := by
      apply continuous_eq_zero_of_test_integrals (hg.sub continuous_const)
      intro v hv hc
      let V : SmoothTest := ⟨v,hv,hc⟩
      have hi := hall V
      dsimp only [m₀,m₁,testIntegral,LinearMap.coe_mk,AddHom.coe_mk] at hi
      change (∫ x, v x*(g x-m₁ w₀))=0
      simp only [mul_sub]
      rw [integral_sub (test_integrable V hg) (test_integrable V continuous_const)]
      simp only [integral_mul_const,mul_one] at hi ⊢
      change (∫ x, V x*g x)=m₁ w₀*(∫ x, V x) at hi
      linarith
    obtain ⟨a,b,hab⟩ := hne
    have ha := congrFun hzero a
    have hb := congrFun hzero b
    exact hab (by dsimp only [Pi.zero_apply] at ha hb; linarith)
  obtain ⟨z,hz₀,hz₁⟩ := hz
  refine ⟨w₀,w₀+z,hw₀,?_,?_⟩
  · change m₀ (w₀+z)=1
    rw [map_add,hz₀,add_zero]
    exact hw₀
  · change m₁ w₀≠m₁ (w₀+z)
    rw [map_add]
    exact fun h => hz₁ (by linarith)

/--
Constructs witnesses with the exact properties `∃ w₀ w₁ : SmoothTest, (∫ x, w₀ x)=1 ∧ (∫ x, w₁
x)=1 ∧ (∫ x, w₀ x/(2*chebyshev2.SineContinuum.n x))≠ (∫ x, w₁
x/(2*chebyshev2.SineContinuum.n x))`.

Use: `chebyshev2.LocalObstruction.sine_nonstationary_test` uses this identity to establish
constructs witnesses with the exact properties `∃ v : SmoothTest, (∫ x, v x)=0 ∧ (∫ x, v x/(2*n
x))=0 ∧ (∫ x, v x*((3/2:ℝ)*n x-g x))≠0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_continuous`,
`chebyshev2.SineContinuum.n_positive`,
`chebyshev2.LocalObstruction.sine_amplitude_tendsto_zero` with the arguments shown in the
proof.
-/
theorem sine_normalization_directions :
    ∃ w₀ w₁ : SmoothTest, (∫ x, w₀ x)=1 ∧ (∫ x, w₁ x)=1 ∧
      (∫ x, w₀ x/(2*chebyshev2.SineContinuum.n x))≠
        (∫ x, w₁ x/(2*chebyshev2.SineContinuum.n x)) := by
  -- Establish continuity hg before using the function at limits or in calculus arguments.
  have hg : Continuous (fun x => 1/(2*chebyshev2.SineContinuum.n x)) :=
    continuous_const.div (continuous_const.mul chebyshev2.SineContinuum.n_continuous)
      (fun x => (mul_pos (by norm_num) (chebyshev2.SineContinuum.n_positive x)).ne')
  have hn : ∃ a b, 1/(2*chebyshev2.SineContinuum.n a)≠1/(2*chebyshev2.SineContinuum.n b) := by
    have hp := chebyshev2.SineContinuum.n_positive 0
    obtain ⟨b,hb⟩ := (sine_amplitude_tendsto_zero.eventually
      (gt_mem_nhds hp)).exists
    refine ⟨0,b,?_⟩
    intro he
    have hi := (inv_inj.mp (by simpa only [one_div] using he))
    linarith
  obtain ⟨w₀,w₁,h₀,h₁,hne⟩ := independent_normalization_directions hg hn
  refine ⟨w₀,w₁,?_,?_,?_⟩
  · simpa [testIntegral] using h₀
  · simpa [testIntegral] using h₁
  · simpa [testIntegral,div_eq_mul_inv] using hne

end
end chebyshev2.LocalObstruction
