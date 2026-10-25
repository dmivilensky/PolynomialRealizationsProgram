import polyak.Levels.Program.Periodic
import polyak.Waves.Finite

/-! Exact finite atomic decomposition; zero-mass atoms are removed. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

theorem periodicGrid_finite {k : ℕ} (hk : 0<k) : (periodicGrid k).Finite := by
  classical
  let f : Frequency→ℤ:=fun ω=>if h:ω∈periodicGrid k then Classical.choose h.2 else 0
  have hf {ω : Frequency} (hω : ω∈periodicGrid k) :
      (k:ℝ)*(ω:ℝ)=(f ω:ℝ)*(2*Real.pi) := by
    simpa only [f,dite_eq_left hω] using Classical.choose_spec hω.2
  apply Set.Finite.of_injOn (f:=f) (t:=Set.Icc (1:ℤ) k) ?_ ?_ (Set.finite_Icc _ _)
  · intro ω hω
    have hj:=hf hω
    have hkR : 0<(k:ℝ):=by exact_mod_cast hk
    have hjpos : 0<(f ω:ℝ):=by nlinarith [mul_pos hkR hω.1,Real.pi_pos]
    have hjle : (f ω:ℝ)≤k:=by nlinarith [ω.property.2,Real.pi_pos]
    constructor
    · have : (0:ℤ)<f ω:=by exact_mod_cast hjpos
      omega
    · exact_mod_cast hjle
  · intro ω hω η hη he
    apply Subtype.ext
    have h1:=hf hω
    have h2:=hf hη
    rw [he] at h1
    have hkR : (k:ℝ)≠0:=by exact_mod_cast (ne_of_gt hk)
    exact mul_left_cancel₀ hkR (h1.trans h2.symm)

/-- Every probability measure carried by a finite set has an exact finite
spectrum presentation with strictly positive masses and distinct atoms. -/
theorem probability_finite_atoms {s : Finset Spectral.Frequency} (ν : Spectral.Spectrum)
    (hs : ∀ᵐc ∂(ν:Measure Spectral.Frequency),c∈s) :
    ∃(J : Type)(_:Fintype J)(w:J→NNReal)(c:J→Spectral.Frequency),
      Function.Injective c ∧ (∀j,0<w j) ∧ (∀j,c j∈s) ∧
      ∃hw : ∑j,w j=1, Waves.finiteSpectrum w c hw=ν := by
  classical
  let t:=s.filter (fun c=>(ν:Measure Spectral.Frequency) {c}≠0)
  let J:Type:={c // c∈t}
  let c:J→Spectral.Frequency:=Subtype.val
  let w:J→NNReal:=fun j=>((ν:Measure Spectral.Frequency) {j.val}).toNNReal
  have hmass : (ν:Measure Spectral.Frequency)=∑j:J,(w j:ENNReal)•Measure.dirac (c j) := by
    have he:=Measure.ae_mem_finset_iff.mp hs
    change (ν:Measure Spectral.Frequency)=∑j:{x // x∈t},
      (ENNReal.toNNReal ((ν:Measure Spectral.Frequency) {j.val}):ENNReal)•Measure.dirac j.val
    rw [Finset.sum_coe_sort t (fun x=>(ENNReal.toNNReal ((ν:Measure Spectral.Frequency) {x}):ENNReal)•Measure.dirac x)]
    simp only [ENNReal.coe_toNNReal (measure_ne_top _ _)]
    nth_rw 1 [he]
    symm
    apply Finset.sum_filter_of_ne
    intro x _ hx hz
    exact hx (by simp [hz])
  have hw : ∑j:J,w j=1 := by
    apply ENNReal.coe_injective
    rw [ENNReal.ofNNReal_finsetSum]
    have hu:=congrArg (fun μ:Measure Spectral.Frequency=>μ Set.univ) hmass
    simpa using hu.symm
  refine ⟨J,inferInstance,w,c,Subtype.val_injective,?_,?_,hw,?_⟩
  · intro j
    exact ENNReal.toNNReal_pos (Finset.mem_filter.mp j.property).2 (measure_ne_top _ _)
  · intro j
    exact (Finset.mem_filter.mp j.property).1
  · apply Subtype.ext
    exact hmass.symm

end polyak.Levels
