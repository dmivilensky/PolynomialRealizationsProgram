import nesterov.Attainment.LimitingDual
import nesterov.Attainment.HullAnalytic
import nesterov.Attainment.HullEndpoint
import nesterov.Attainment.HullMoment
import nesterov.Attainment.Endpoints

/-! One analytic limiting dual confines every optimal probability spectrum
to one finite common carrier strictly inside the physical frequency interval. -/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace nesterov.Attainment
open Spectral

def oneFrequency : Frequency := ⟨1,by norm_num⟩

def dualZeros (lo hi : ℝ) (hlo : 0 < lo) (s : LagParameter lo hi) (d : DualPoint lo hi) :
    Set Frequency := {c | d.2 (s,physicalAngle lo hlo c)=0}

theorem dualZeros_finite (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) {d : DualPoint lo hi} (hd : d ∈ polynomialDualHull u p lo hi σ hlo)
    (hg : g (polynomialPair u p (σ*s)) oneFrequency < 0) :
    (dualZeros lo hi hlo s d).Finite := by
  let f := polyak.Spectral.windowExtension (restrictSymbolCLM lo hi s d)
  let A : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) Real.pi
  have hA : IsCompact A := isCompact_Icc.image Complex.continuous_ofReal
  have hAU : A ⊆ interior (LagWindow lo) := by
    rintro _ ⟨ω,hω,rfl⟩
    exact polyak.Spectral.real_mem_interior_lagWindow hlo hω
  have hz₀ : (0 : ℂ) ∈ interior (LagWindow lo) :=
    polyak.Spectral.real_mem_interior_lagWindow hlo ⟨le_rfl,Real.pi_pos.le⟩
  have hf₀ : f 0 ≠ 0 := by
    have hn := dualHull_endpoint_neg u p lo hi σ hlo s oneFrequency (Or.inl rfl) hg hd
    intro hf
    have he : f 0 = d.2 (s,physicalAngle lo hlo oneFrequency) := by
      simp only [f,polyak.Spectral.windowExtension,dite_eq_left (interior_subset hz₀)]
      simp [restrictSymbolCLM,parameterSlice,physicalAngle,polyak.Spectral.dualAngle,oneFrequency]
    rw [he] at hf
    rw [hf,Complex.zero_re] at hn
    exact (lt_irrefl (0:ℝ)) hn
  have hz := polyak.Spectral.finite_zeros_on_compact isOpen_interior
    (polyak.Spectral.convex_lagWindow lo).interior.isPreconnected hA hAU
    (polynomial_dualHull_holomorphic u p lo hi σ hlo s hd) hz₀ hf₀
  let angle : Frequency → ℂ := fun c => (Real.arccos c : ℂ)
  have hinj : Function.Injective angle := by
    intro c c' he
    apply Subtype.ext
    have he' : Real.arccos (c:ℝ)=Real.arccos (c':ℝ) := Complex.ofReal_injective he
    have hh := congrArg Real.cos he'
    simpa only [Real.cos_arccos c.property.1 c.property.2,
      Real.cos_arccos c'.property.1 c'.property.2] using hh
  have himage : angle '' dualZeros lo hi hlo s d ⊆ {w∈A | f w=0} := by
    rintro _ ⟨c,hc,rfl⟩
    refine ⟨⟨Real.arccos c,⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩,rfl⟩,?_⟩
    have he := polyak.Spectral.windowExtension_coe (restrictSymbolCLM lo hi s d) (physicalAngle lo hlo c)
    exact he.trans hc
  exact Set.Finite.of_finite_image (hz.subset himage) hinj.injOn

theorem dualZeros_interior (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) {d : DualPoint lo hi} (hd : d ∈ polynomialDualHull u p lo hi σ hlo)
    (hg : ∀ c : Frequency, (c:ℝ)=1 ∨ (c:ℝ)= -1 → g (polynomialPair u p (σ*s)) c < 0)
    {c : Frequency} (hc : c ∈ dualZeros lo hi hlo s d) : -1 < (c:ℝ) ∧ (c:ℝ) < 1 := by
  have hleft : (c:ℝ) ≠ -1 := by
    intro he
    have hn := dualHull_endpoint_neg u p lo hi σ hlo s c (Or.inr he) (hg c (Or.inr he)) hd
    rw [hc,Complex.zero_re] at hn
    exact (lt_irrefl (0:ℝ)) hn
  have hright : (c:ℝ) ≠ 1 := by
    intro he
    have hn := dualHull_endpoint_neg u p lo hi σ hlo s c (Or.inl he) (hg c (Or.inl he)) hd
    rw [hc,Complex.zero_re] at hn
    exact (lt_irrefl (0:ℝ)) hn
  exact ⟨lt_of_le_of_ne c.property.1 hleft.symm,lt_of_le_of_ne c.property.2 hright⟩

theorem ExponentFrame.feasible_to_positive {t : ℝ} (F : ExponentFrame t)
    {a : SymbolPair} {ν : Spectrum} {C : ℝ} (h : Feasible a t ν C) :
    Feasible a (F.center : ℝ) ν (F.sign*C) := by
  have ht := F.physical
  rcases F.sign_cases with hs | hs
  · have he : (F.center : ℝ)=t := by simpa only [ExponentFrame.center,hs,one_mul] using ht
    simpa only [hs,one_mul,he] using h
  · have he : -(F.center : ℝ)=t := by simpa only [ExponentFrame.center,hs,neg_one_mul] using ht
    have hh : Feasible a (-(F.center : ℝ)) ν (-(-C)) := by simpa only [he,neg_neg] using h
    have hp := (feasible_neg_t_iff a (F.center : ℝ) (-C) ν).mp hh
    simpa only [hs,neg_one_mul] using hp

/-- Lemma finite: one finite interior carrier works for every pair at T.
No atomicity or finite active set was assumed in constructing the limiting dual. -/
theorem exists_finite_boundary_carrier (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L) :
    ∃ F : Set Frequency, F.Finite ∧ (∀ c∈F, -1 < (c:ℝ) ∧ (c:ℝ) < 1) ∧
      ∀ (ν : Spectrum) (C : ℝ), Feasible (M.symbolPair μ L (Closure.T M μ L))
        (Closure.T M μ L) ν C → (ν : Measure Frequency) Fᶜ=0 := by
  obtain ⟨F,d,hd,hcharge,hneg⟩ := exists_limiting_dual_at_T M hμ hμL ht
  have hphys : F.sign*(F.center : ℝ)=Closure.T M μ L := F.physical
  have hpair : polynomialPair M.queryPolynomial (M.normalizedPolynomial μ L) (F.sign*F.center) =
      M.symbolPair μ L (Closure.T M μ L) := by
    rw [hphys]
    rfl
  have hgap (c : Frequency) (hc : (c:ℝ)=1 ∨ (c:ℝ)= -1) :
      g (polynomialPair M.queryPolynomial (M.normalizedPolynomial μ L) (F.sign*F.center)) c < 0 := by
    rw [hpair]
    exact gap_endpoint_neg M hμ hμL htq c hc
  refine ⟨dualZeros F.lo F.hi (half_pos F.radius_pos) F.center d,
    dualZeros_finite _ _ _ _ _ _ _ hd (hgap oneFrequency (Or.inl rfl)),
    fun c hc => dualZeros_interior _ _ _ _ _ _ _ hd hgap hc, fun ν C h => ?_⟩
  have hpos := F.feasible_to_positive h
  rw [← hpair] at hpos
  have hm := dualHull_moment_nonneg _ _ _ _ _ _ _ hpos hd
  rw [hcharge,zero_mul,add_zero] at hm
  exact measure_compl_dualZeros_eq_zero F.lo F.hi (half_pos F.radius_pos) F.center d ν hneg
    (fun c => dualHull_trace_im_zero _ _ _ _ _ _ _ hd c) hm

end nesterov.Attainment
