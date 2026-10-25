import polyak.General.IQC.Apriori
import polyak.General.IQC.ZeroExtension
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Appendix D, Lemma homotopy: bounded measurable frequency IQCs induce
bounded time-domain bilinear forms. The pointwise frequency graph inequality
is integrated in L2 and transported by a unitary transform; no time-domain
gap is postulated. The official normalized AddCircle Fourier basis supplies
the scalar whole-line Fourier unitary. -/
noncomputable section
namespace polyak.General.IQC
namespace Fourier
open MeasureTheory
open scoped ENNReal

variable {Ω V H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

abbrev FSpace (μ : Measure Ω) (V : Type*) [NormedAddCommGroup V] := Lp V 2 μ
abbrev Coefficient (μ : Measure Ω) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  Lp (V→L[ℝ]V) ∞ μ

/-- Multiplication by an essentially bounded measurable operator field.
Hölder with exponents infinity,2,2 proves boundedness directly. -/
def multiply (P : Coefficient μ V) : FSpace μ V→L[ℝ]FSpace μ V :=
  ((ContinuousLinearMap.apply ℝ V).flip.holderL μ ∞ 2 2) P

theorem multiply_ae (P : Coefficient μ V) (f : FSpace μ V) :
    multiply P f=ᵐ[μ] fun ω=>P ω (f ω) :=
  (ContinuousLinearMap.apply ℝ V).flip.coeFn_holder P f

/-- All four bounded blocks of the frequency-domain IQC. Hermitian fields
are included; boundedness itself does not require symmetry. -/
structure BoundedIQC (μ : Measure Ω) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  p00 : Coefficient μ V
  p01 : Coefficient μ V
  p10 : Coefficient μ V
  p11 : Coefficient μ V

/-- Literal real quadratic form of the block operator at a frequency. -/
def pointValue (P : BoundedIQC μ V) (ω : Ω) (x y : V) : ℝ :=
  inner ℝ x (P.p00 ω x)+inner ℝ x (P.p01 ω y)+
    inner ℝ y (P.p10 ω x)+inner ℝ y (P.p11 ω y)

def blockForm (U : H→ₗᵢ[ℝ] FSpace μ V) (P : Coefficient μ V)
    (i j : (H×H)→L[ℝ]H) : (H×H)→L[ℝ](H×H)→L[ℝ]ℝ :=
  (innerSL ℝ).bilinearComp (U.toContinuousLinearMap.comp i)
    ((multiply P).comp (U.toContinuousLinearMap.comp j))

/-- The bounded bilinear time-domain IQC is constructed, rather than assumed. -/
def bilinearIQC (U : H→ₗᵢ[ℝ] FSpace μ V) (P : BoundedIQC μ V) : BilinearIQC H :=
  blockForm U P.p00 (ContinuousLinearMap.fst ℝ H H) (ContinuousLinearMap.fst ℝ H H)+
  blockForm U P.p01 (ContinuousLinearMap.fst ℝ H H) (ContinuousLinearMap.snd ℝ H H)+
  blockForm U P.p10 (ContinuousLinearMap.snd ℝ H H) (ContinuousLinearMap.fst ℝ H H)+
  blockForm U P.p11 (ContinuousLinearMap.snd ℝ H H) (ContinuousLinearMap.snd ℝ H H)

private theorem inner_multiply_integral (P : Coefficient μ V) (f g : FSpace μ V) :
    inner ℝ f (multiply P g)=∫ ω,inner ℝ (f ω) (P ω (g ω)) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae P g] with ω hω
  rw [hω]

private theorem inner_multiply_integrable (P : Coefficient μ V) (f g : FSpace μ V) :
    Integrable (fun ω=>inner ℝ (f ω) (P ω (g ω))) μ := by
  apply (L2.integrable_inner (𝕜:=ℝ) f (multiply P g)).congr
  filter_upwards [multiply_ae P g] with ω hω
  rw [hω]

/-- Equality with the frequency integral, including all cross terms. -/
theorem iqcValue_eq_integral (U : H→ₗᵢ[ℝ] FSpace μ V) (P : BoundedIQC μ V) (x y : H) :
    iqcValue (bilinearIQC U P) x y=∫ ω,pointValue P ω (U x ω) (U y ω) ∂μ := by
  simp only [iqcValue,bilinearIQC,add_apply,blockForm,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,ContinuousLinearMap.snd,
    innerSL_apply_apply,LinearIsometry.coe_toContinuousLinearMap]
  rw [inner_multiply_integral,inner_multiply_integral,inner_multiply_integral,inner_multiply_integral]
  simp only [pointValue]
  have h0 := inner_multiply_integrable P.p00 (U x) (U x)
  have h1 := inner_multiply_integrable P.p01 (U x) (U y)
  have h2 := inner_multiply_integrable P.p10 (U y) (U x)
  have h3 := inner_multiply_integrable P.p11 (U y) (U y)
  have h01 := integral_add h0 h1
  have h012 := integral_add (h0.add h1) h2
  have h0123 := integral_add ((h0.add h1).add h2) h3
  simp only [Pi.add_apply] at h01 h012 h0123
  rw [h0123,h012,h01]
  rfl


/-- The actual bounded plant associated with its frequency multiplier. -/
def plant (U : H≃ₗᵢ[ℝ] FSpace μ V) (G : Coefficient μ V) : H→L[ℝ]H :=
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((multiply G).comp U.toContinuousLinearEquiv.toContinuousLinearMap)

theorem transform_plant (U : H≃ₗᵢ[ℝ] FSpace μ V) (G : Coefficient μ V) (z : H) :
    U (plant U G z)=multiply G (U z) := by
  simp only [plant,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.apply_symm_apply]

/-- The source frequency inequality, integrated and transported to time.
It is enough to hold almost everywhere and for all vector channels. -/
theorem graph_gap_of_pair (U : H→ₗᵢ[ℝ] FSpace μ V) (P : BoundedIQC μ V)
    (G : Coefficient μ V) {ε : ℝ}
    (hgap : ∀ᵐ ω ∂μ,∀ z : V,pointValue P ω (G ω z) z≤ -ε*‖z‖^2) (x z : H)
    (htransform : U x=multiply G (U z)) :
    iqcValue (bilinearIQC U P) x z≤ -ε*‖z‖^2 := by
  rw [iqcValue_eq_integral]
  have hz : ∀ᵐ ω ∂μ,U x ω=G ω (U z ω) := by
    rw [htransform]
    exact multiply_ae G (U z)
  have hleft : Integrable (fun ω=>pointValue P ω (U x ω) (U z ω)) μ :=
    (((inner_multiply_integrable P.p00 (U x) (U x)).add
      (inner_multiply_integrable P.p01 (U x) (U z))).add
      (inner_multiply_integrable P.p10 (U z) (U x))).add
      (inner_multiply_integrable P.p11 (U z) (U z))
  have hright : Integrable (fun ω=> -ε*‖U z ω‖^2) μ := by
    have hh := L2.integrable_inner (𝕜:=ℝ) (U z) (U z)
    simpa only [real_inner_self_eq_norm_sq] using hh.const_mul (-ε)
  calc
    _≤∫ ω,-ε*‖U z ω‖^2 ∂μ := integral_mono_ae hleft hright (by
      filter_upwards [hgap,hz] with ω hω hzω
      rw [hzω]
      exact hω (U z ω))
    _= -ε*‖z‖^2 := by
      have hn : (∫ ω,‖U z ω‖^2 ∂μ)=‖z‖^2 := by
        calc
          _=inner ℝ (U z) (U z) := by rw [L2.inner_def]; simp only [real_inner_self_eq_norm_sq]
          _=‖U z‖^2 := real_inner_self_eq_norm_sq _
          _=‖z‖^2 := by rw [U.norm_map]
      rw [integral_const_mul,hn]

/-- The source frequency graph inequality transported through an isometric transform. -/
theorem graph_gap_of_transform (U : H→ₗᵢ[ℝ] FSpace μ V) (P : BoundedIQC μ V)
    (G : Coefficient μ V) (T : H→L[ℝ]H)
    (htransform : ∀ z,U (T z)=multiply G (U z)) {ε : ℝ}
    (hgap : ∀ᵐ ω ∂μ,∀ z : V,pointValue P ω (G ω z) z≤ -ε*‖z‖^2) (z : H) :
    iqcValue (bilinearIQC U P) (T z) z≤ -ε*‖z‖^2 :=
  graph_gap_of_pair U P G hgap (T z) z (htransform z)

/-- The unitary conjugate plant is a special case of the isometric transform theorem. -/
theorem graph_gap_of_frequency (U : H≃ₗᵢ[ℝ] FSpace μ V) (P : BoundedIQC μ V)
    (G : Coefficient μ V) {ε : ℝ}
    (hgap : ∀ᵐ ω ∂μ,∀ z : V,pointValue P ω (G ω z) z≤ -ε*‖z‖^2) (z : H) :
    iqcValue (bilinearIQC U.toLinearIsometry P) (plant U G z) z≤ -ε*‖z‖^2 :=
  graph_gap_of_transform U.toLinearIsometry P G (plant U G) (transform_plant U G) hgap z

/-- A bounded measurable complex scalar is a bounded real operator field. -/
def scalarOperator (p : Lp ℂ ∞ μ) : Coefficient μ ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℂ).compLp p

theorem scalarOperator_ae (p : Lp ℂ ∞ μ) :
    ∀ᵐ ω ∂μ,∀ z : ℂ,scalarOperator p ω z=p ω*z := by
  have he := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ→L[ℝ](ℂ→L[ℝ]ℂ)).coeFn_compLp p
  filter_upwards [he] with ω hω
  intro z
  rw [show scalarOperator p ω=(ContinuousLinearMap.lsmul ℝ ℂ) (p ω) from hω]
  rfl

/-- The literal 2x2 complex coefficient field, acting through bounded real operators. -/
def scalarIQC (P : Fin 2→Fin 2→Lp ℂ ∞ μ) : BoundedIQC μ ℂ :=
  ⟨scalarOperator (P 0 0),scalarOperator (P 0 1),scalarOperator (P 1 0),scalarOperator (P 1 1)⟩

/-- The source normalized Hermitian graph expression [g;1]*Pi*[g;1], taking its real part. -/
def matrixGraphValue (p00 p01 p10 p11 g : ℂ) : ℝ :=
  (star g*(p00*g+p01)+(p10*g+p11)).re

private theorem scalar_graph_homogeneous (p00 p01 p10 p11 g z : ℂ) :
    inner ℝ (g*z) (p00*(g*z))+inner ℝ (g*z) (p01*z)+
      inner ℝ z (p10*(g*z))+inner ℝ z (p11*z)=
      Complex.normSq z*matrixGraphValue p00 p01 p10 p11 g := by
  simp only [matrixGraphValue,Complex.star_def,Complex.inner,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

/-- The normalized scalar source inequality already supplies the all-vector graph gap. -/
theorem scalar_frequency_gap (P : Fin 2→Fin 2→Lp ℂ ∞ μ) (G : Lp ℂ ∞ μ) {ε : ℝ}
    (hgap : ∀ᵐ ω ∂μ,matrixGraphValue (P 0 0 ω) (P 0 1 ω) (P 1 0 ω) (P 1 1 ω) (G ω)≤ -ε) :
    ∀ᵐ ω ∂μ,∀ z : ℂ,pointValue (scalarIQC P) ω (scalarOperator G ω z) z≤ -ε*‖z‖^2 := by
  filter_upwards [hgap,scalarOperator_ae G,scalarOperator_ae (P 0 0),
    scalarOperator_ae (P 0 1),scalarOperator_ae (P 1 0),scalarOperator_ae (P 1 1)]
    with ω hω hG h00 h01 h10 h11
  intro z
  simp only [pointValue,scalarIQC,hG,h00,h01,h10,h11]
  rw [scalar_graph_homogeneous]
  have hh := mul_le_mul_of_nonneg_left hω (Complex.normSq_nonneg z)
  simpa only [Complex.normSq_eq_norm_sq,mul_comm] using hh

/-- Full scalar frequency-to-time graph implication under the literal normalized hypothesis. -/
theorem scalar_graph_gap_of_frequency (U : H≃ₗᵢ[ℝ] FSpace μ ℂ)
    (P : Fin 2→Fin 2→Lp ℂ ∞ μ) (G : Lp ℂ ∞ μ) {ε : ℝ}
    (hgap : ∀ᵐ ω ∂μ,matrixGraphValue (P 0 0 ω) (P 0 1 ω) (P 1 0 ω) (P 1 1 ω) (G ω)≤ -ε)
    (z : H) : iqcValue (bilinearIQC U.toLinearIsometry (scalarIQC P)) (plant U (scalarOperator G) z) z≤ -ε*‖z‖^2 :=
  graph_gap_of_frequency U (scalarIQC P) (scalarOperator G) (scalar_frequency_gap P G hgap) z

local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

abbrev ScalarTime := lp (fun _ : ℤ=>ℂ) 2
abbrev ScalarFrequency := Lp ℂ 2 (AddCircle.haarAddCircle (T:=2*Real.pi))

/-- The official normalized Haar Fourier transform, viewed as a real unitary.
The coefficient-to-function direction is fourierBasis.repr.symm. -/
def scalarUnitary : ScalarTime≃ₗᵢ[ℝ]ScalarFrequency where
  toLinearEquiv := (fourierBasis (T:=2*Real.pi)).repr.symm.toLinearEquiv.restrictScalars ℝ
  norm_map' x := (fourierBasis (T:=2*Real.pi)).repr.symm.norm_map x

/-- The causal Fourier transform is the actual isometric zero extension,
followed by the official whole-line unitary. No surjectivity is asserted. -/
def halfLineTransform : SequenceSpace ℂ→ₗᵢ[ℝ]ScalarFrequency :=
  scalarUnitary.toLinearIsometry.comp zeroExtendLI

/-- Fourier transformation in each finite spatial coordinate. -/
def coordinateUnitary (d : ℕ) :
    EuclideanSpace ScalarTime (Fin d)≃ₗᵢ[ℝ]EuclideanSpace ScalarFrequency (Fin d) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _=>scalarUnitary)

@[simp] theorem coordinateUnitary_apply (d : ℕ) (x : EuclideanSpace ScalarTime (Fin d))
    (i : Fin d) : coordinateUnitary d x i=scalarUnitary (x i) := rfl

/-- The pointwise scalar graph gap acts blockwise in every finite dimension.
No dimension-dependent constant is lost in the Fourier/Parseval passage. -/
theorem componentwise_graph_gap (d : ℕ)
    (P : BoundedIQC (AddCircle.haarAddCircle (T:=2*Real.pi)) ℂ)
    (G : Coefficient (AddCircle.haarAddCircle (T:=2*Real.pi)) ℂ) {ε : ℝ}
    (hgap : ∀ᵐ ω ∂AddCircle.haarAddCircle (T:=2*Real.pi),∀ z : ℂ,
      pointValue P ω (G ω z) z≤ -ε*‖z‖^2) (x : EuclideanSpace ScalarTime (Fin d)) :
    ∑ i,iqcValue (bilinearIQC scalarUnitary.toLinearIsometry P) (plant scalarUnitary G (x i)) (x i)≤ -ε*‖x‖^2 := by
  have hh : ∑ i,iqcValue (bilinearIQC scalarUnitary.toLinearIsometry P) (plant scalarUnitary G (x i)) (x i)≤
      ∑ i,-ε*‖x i‖^2 :=
    Finset.sum_le_sum (fun i _=>graph_gap_of_frequency scalarUnitary P G hgap (x i))
  rw [← Finset.mul_sum,PiLp.norm_sq_eq_of_L2] at *
  exact hh

end Fourier
end polyak.General.IQC
