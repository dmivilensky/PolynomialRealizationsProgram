import nesterov.Attainment.LimitingDual
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Ultrafilter

/-! The compactified dual is represented by an actual probability measure
on the two distinct signed lag families. Only ordinary weak compactness is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology OnePoint BigOperators NNReal ENNReal
namespace nesterov.Attainment
open Spectral

instance dualLabelMeasurableSpace : MeasurableSpace DualLabel := borel DualLabel
instance dualLabelBorelSpace : BorelSpace DualLabel := ⟨rfl⟩

abbrev DualMeasure := ProbabilityMeasure DualLabel

def finiteDualMeasure {I : Type*} [Fintype I] (w : I → ℝ≥0) (l : I → DualLabel)
    (hw : ∑ i,w i=1) : DualMeasure :=
  ⟨∑ i,(w i : ℝ≥0∞) • Measure.dirac (l i),
    ⟨by simp [← ENNReal.ofNNReal_finsetSum,hw]⟩⟩

theorem finiteDualMeasure_integral {I : Type*} [Fintype I]
    (w : I → ℝ≥0) (l : I → DualLabel) (hw : ∑ i,w i=1) (f : DualLabel → ℝ) :
    (∫ a,f a ∂finiteDualMeasure w l hw)=∑ i,(w i : ℝ)*f (l i) := by
  have hi (i : I) : Integrable f ((w i : ℝ≥0∞) • Measure.dirac (l i)) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  simpa [finiteDualMeasure,integral_smul_measure,NNReal.smul_def,smul_eq_mul] using
    (integral_finsetSum_measure (s := Finset.univ) (fun i _ => hi i))

def certificateLabel {a : SymbolPair} {s : ℝ} (cert : StrictCertificate a s) :
    CertificateIndices cert → DualLabel
  | .inl b => (b,∞)
  | .inr (n,b) => (b,((n.val-1 : ℕ) : OnePoint ℕ))

def normalizedMass {a : SymbolPair} {s : ℝ} (cert : StrictCertificate a s)
    (hs : 0 < s) (i : CertificateIndices cert) : ℝ≥0 :=
  ⟨certificateMass cert i/(∑ j,certificateMass cert j),
    div_nonneg (certificateMass_nonneg cert hs i) (certificateMass_sum_pos cert hs).le⟩

theorem normalizedMass_sum {a : SymbolPair} {s : ℝ} (cert : StrictCertificate a s)
    (hs : 0 < s) : ∑ i,normalizedMass cert hs i=1 := by
  apply NNReal.coe_injective
  push_cast
  change (∑ i,certificateMass cert i/(∑ j,certificateMass cert j))=1
  rw [← Finset.sum_div,div_self (ne_of_gt (certificateMass_sum_pos cert hs))]

def certificateMeasure {a : SymbolPair} {s : ℝ} (cert : StrictCertificate a s) (hs : 0 < s) : DualMeasure :=
  finiteDualMeasure (normalizedMass cert hs) (certificateLabel cert) (normalizedMass_sum cert hs)

theorem certificateGenerator_eq_label {a : SymbolPair} {s : ℝ} (cert : StrictCertificate a s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) (i : CertificateIndices cert) :
    certificateGenerator cert u p lo hi σ hlo i =
      dualLabelMap lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) (certificateLabel cert i) := by
  rcases i with b | ⟨n,b⟩ <;> cases b <;> rfl

theorem certificateMeasure_integral {a : SymbolPair} {s : ℝ} (cert : StrictCertificate a s) (hs : 0 < s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) (L : DualPoint lo hi →L[ℝ] ℝ) :
    (∫ l,L (dualLabelMap lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) l)
      ∂certificateMeasure cert hs) = L (normalizedCertificate cert u p lo hi σ hlo) := by
  rw [certificateMeasure,finiteDualMeasure_integral]
  simp_rw [← certificateGenerator_eq_label]
  rw [normalizedCertificate,certificateCombination,map_smul,map_sum]
  simp only [map_smul,smul_eq_mul,normalizedMass]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change certificateMass cert i/(∑ j,certificateMass cert j) *
    L (certificateGenerator cert u p lo hi σ hlo i) = _
  ring

/-- Compactness of both the Banach symbols and actual dual probability measures
retains their weak barycenter identity for every continuous linear functional. -/
theorem exists_limiting_dual_measure_of_sequence (u p : Polynomial ℝ) (lo hi σ : ℝ)
    (hlo : 0 < lo) (s₀ : LagParameter lo hi) (s : ℕ → LagParameter lo hi)
    (hs : Tendsto s atTop (𝓝 s₀))
    (hcert : ∀ n, Nonempty (StrictCertificate (polynomialPair u p (σ*s n)) (s n))) :
    ∃ (d : DualPoint lo hi) (Λ : DualMeasure), d ∈ polynomialDualHull u p lo hi σ hlo ∧
      d.1=0 ∧ (∀ c : Frequency,(d.2 (s₀,physicalAngle lo hlo c)).re ≤ 0) ∧
      ∀ L : DualPoint lo hi →L[ℝ] ℝ,
        (∫ l,L (dualLabelMap lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) l) ∂Λ)=L d := by
  classical
  let cert (n : ℕ) : StrictCertificate (polynomialPair u p (σ*s n)) (s n) := Classical.choice (hcert n)
  let d : ℕ → DualPoint lo hi := fun n => normalizedCertificate (cert n) u p lo hi σ hlo
  let Λ : ℕ → DualMeasure := fun n => certificateMeasure (cert n) (hlo.trans_le (s n).property.1)
  let K := polynomialDualHull u p lo hi σ hlo ×ˢ (Set.univ : Set DualMeasure)
  have hK : IsCompact K := (isCompact_dualHull lo hi hlo _ _).prod isCompact_univ
  have hmem : ∀ n,(d n,Λ n)∈K := fun n =>
    ⟨normalizedCertificate_mem (cert n) (hlo.trans_le (s n).property.1) u p lo hi σ hlo,Set.mem_univ _⟩
  obtain ⟨x,hx,hcl⟩ := hK.exists_mapClusterPt (u := fun n => (d n,Λ n)) (f := atTop) (by
    rw [Filter.map_le_iff_le_comap,Filter.comap_principal,Filter.le_principal_iff]
    exact Eventually.of_forall hmem)
  obtain ⟨U,hU,hlim⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have hdlim := continuous_fst.tendsto x |>.comp hlim
  have hΛlim := continuous_snd.tendsto x |>.comp hlim
  refine ⟨x.1,x.2,hx.1,?_,?_,fun L => ?_⟩
  · exact (isClosed_eq continuous_fst continuous_const).mem_of_tendsto hdlim
      (Eventually.of_forall (fun n => normalizedCertificate_charge (cert n) u p lo hi σ hlo))
  · intro c
    have heval : Continuous (fun q : LagParameter lo hi × DualPoint lo hi =>
        (q.2.2 (q.1,physicalAngle lo hlo c)).re) := Complex.continuous_re.comp
      (continuous_eval.comp (continuous_snd.snd.prodMk (continuous_fst.prodMk continuous_const)))
    have ht := (heval.tendsto (s₀,x.1)).comp ((hs.mono_left hU).prodMk_nhds hdlim)
    apply le_of_tendsto ht
    apply Eventually.of_forall
    intro n
    dsimp [d]
    rw [normalizedCertificate_evaluate]
    exact div_nonpos_of_nonpos_of_nonneg
      ((cert n).strict c |>.trans (neg_nonpos.mpr (cert n).ε_pos.le))
      (certificateMass_sum_pos (cert n) (hlo.trans_le (s n).property.1)).le
  · let f : C(DualLabel,ℝ) :=
      ⟨fun l => L (dualLabelMap lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) l),
        L.continuous.comp (dualLabelMap lo hi hlo _ _).continuous⟩
    have ht := ((ProbabilityMeasure.continuous_integral_continuousMap f).tendsto x.2).comp hΛlim
    have heq := L.continuous.tendsto x.1 |>.comp hdlim
    apply tendsto_nhds_unique ht
    convert heq using 1
    funext n
    exact certificateMeasure_integral (cert n) (hlo.trans_le (s n).property.1) u p lo hi σ hlo L

end nesterov.Attainment
