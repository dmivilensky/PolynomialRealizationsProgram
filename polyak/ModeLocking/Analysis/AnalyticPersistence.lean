import polyak.ModeLocking.Analysis.Persistence
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Joint analyticity on the base compact frequency slice supplies one
parameter neighborhood with genuine joint C0 and frequency C2 continuity. -/
noncomputable section
namespace polyak.ModeLocking.Analysis
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def frequencyDerivative (f : E×ℝ → ℝ) (p : E×ℝ) : ℝ :=
  deriv (fun x => f (p.1,x)) p.2

theorem contDiffAt_frequencyDerivative {f : E×ℝ → ℝ} {p : E×ℝ}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (frequencyDerivative f) p := by
  have hcomp : ContDiffAt ℝ ∞ (fun z : (E×ℝ)×ℝ => f (z.1.1,z.2)) (p,p.2) :=
    hf.comp _ (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd := ContDiffAt.fderiv (f := fun (z : E×ℝ) (x : ℝ) => f (z.1,x))
    (g := fun z : E×ℝ => z.2) hcomp contDiffAt_snd
    (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)
  have hh := hd.clm_apply (contDiffAt_const (c := (1:ℝ)))
  change ContDiffAt ℝ ∞ (fun z : E×ℝ => (fderiv ℝ (fun x => f (z.1,x)) z.2) 1) p
  exact hh

theorem continuousAt_frequencySecond {f : E×ℝ → ℝ} {p : E×ℝ}
    (hf : ContDiffAt ℝ ∞ f p) :
    ContinuousAt (fun z : E×ℝ => iteratedDeriv 2 (fun x => f (z.1,x)) z.2) p := by
  have hh := (contDiffAt_frequencyDerivative (contDiffAt_frequencyDerivative hf)).continuousAt
  have he : frequencyDerivative (frequencyDerivative f) =
      (fun z : E×ℝ => iteratedDeriv 2 (fun x => f (z.1,x)) z.2) := by
    funext z
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rfl
  rw [he] at hh
  exact hh

/-- No derivative-continuity premise remains: it follows from analyticity
on the compact base slice and a single open parameter neighborhood. -/
theorem exists_analytic_slice_neighborhood {f : E×ℝ → ℝ} {p0 : E} {a b : ℝ}
    (hf : ∀ x ∈ Icc a b, AnalyticAt ℝ f (p0,x)) :
    ∃ U : Set E, IsOpen U ∧ p0∈U ∧
      ContinuousOn f (U×ˢIcc a b) ∧
      ContinuousOn (fun z : E×ℝ => iteratedDeriv 2 (fun x => f (z.1,x)) z.2) (U×ˢIcc a b) ∧
      (∀ p∈U, ∀ x∈Icc a b, ContDiffAt ℝ 2 (fun x => f (p,x)) x) := by
  obtain ⟨U,V,hU,_hV,hpU,hCV,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p0)) isCompact_Icc (isOpen_analyticAt ℝ f)
    (show ({p0} : Set E)×ˢIcc a b ⊆ {z | AnalyticAt ℝ f z} from by
      rintro ⟨p,x⟩ ⟨hp,hx⟩
      rcases mem_singleton_iff.mp hp with rfl
      exact hf x hx)
  have hanalytic (p : E) (hp : p∈U) (x : ℝ) (hx : x∈Icc a b) :
      AnalyticAt ℝ f (p,x) := hUV ⟨hp,hCV hx⟩
  refine ⟨U,hU,hpU (mem_singleton p0),?_,?_,?_⟩
  · intro z hz
    exact (hanalytic z.1 hz.1 z.2 hz.2).continuousAt.continuousWithinAt
  · intro z hz
    exact (continuousAt_frequencySecond (hanalytic z.1 hz.1 z.2 hz.2).contDiffAt).continuousWithinAt
  · intro p hp x hx
    exact ((hanalytic p hp x hx).contDiffAt.comp x
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by exact le_top)

variable {X : Type*} [TopologicalSpace X]

theorem NegativeJetCover.eventually_persist_of_eventual_jets
    {f : X → ℝ → ℝ} {p0 : X} {a b : ℝ} {Z : Finset ℝ}
    (D : NegativeJetCover a b Z (f p0)) {U : Set X} (hU : U∈𝓝 p0)
    (hc : ContinuousOn f.uncurry (U×ˢIcc a b))
    (hc2 : ContinuousOn (fun p : X×ℝ => iteratedDeriv 2 (f p.1) p.2) (U×ˢIcc a b))
    (hsm : ∀ p∈U, ∀ x∈Icc a b, ContDiffAt ℝ 2 (f p) x)
    (hjets : ∀ᶠ p in 𝓝 p0, ∀ z∈Z, f p z=0 ∧ deriv (f p) z=0) :
    ∀ᶠ p in 𝓝 p0, Nonempty (NegativeJetCover a b Z (f p)) := by
  let W := U ∩ {p | ∀ z∈Z, f p z=0 ∧ deriv (f p) z=0}
  have hW : W∈𝓝 p0 := inter_mem hU hjets
  have hWsub : W⊆U := inter_subset_left
  have hd := D.eventually_persist (mem_of_mem_nhds hW)
    (hc.mono (prod_mono hWsub Subset.rfl))
    (hc2.mono (prod_mono hWsub Subset.rfl))
    (fun p hp => hsm p hp.1)
    (fun p hp z hz => (hp.2 z hz).1)
    (fun p hp z hz => (hp.2 z hz).2)
  rwa [nhdsWithin_eq_nhds.mpr hW] at hd

/-- The parameter space used by the mathematical application may be an
arbitrary topological space, such as the actual tuning subtype. Only its map
to ambient analytic coordinates must be continuous. -/
theorem NegativeJetCover.eventually_persist_of_analytic_pullback
    {f : E×ℝ → ℝ} {φ : X → E} {p0 : X} {a b : ℝ} {Z : Finset ℝ}
    (D : NegativeJetCover a b Z (fun x => f (φ p0,x)))
    (hφ : Continuous φ)
    (hf : ∀ x∈Icc a b, AnalyticAt ℝ f (φ p0,x))
    (hjets : ∀ᶠ p in 𝓝 p0, ∀ z∈Z,
      f (φ p,z)=0 ∧ deriv (fun x => f (φ p,x)) z=0) :
    ∀ᶠ p in 𝓝 p0, Nonempty (NegativeJetCover a b Z (fun x => f (φ p,x))) := by
  obtain ⟨U,hU,hpU,hc,hc2,hsm⟩ := exists_analytic_slice_neighborhood hf
  let V := φ ⁻¹' U
  have hV : V∈𝓝 p0 := hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)
  have hmap : Continuous (fun z : X×ℝ => (φ z.1,z.2)) :=
    (hφ.comp continuous_fst).prodMk continuous_snd
  let g : X → ℝ → ℝ := fun p x => f (φ p,x)
  have hmaps : MapsTo (fun z : X×ℝ => (φ z.1,z.2)) (V×ˢIcc a b) (U×ˢIcc a b) :=
    fun z hz => ⟨hz.1,hz.2⟩
  have hcg : ContinuousOn g.uncurry (V×ˢIcc a b) := by
    change ContinuousOn (f ∘ (fun z : X×ℝ => (φ z.1,z.2))) (V×ˢIcc a b)
    exact hc.comp hmap.continuousOn hmaps
  have hc2g : ContinuousOn (fun z : X×ℝ => iteratedDeriv 2 (g z.1) z.2) (V×ˢIcc a b) := by
    change ContinuousOn ((fun z : E×ℝ => iteratedDeriv 2 (fun x => f (z.1,x)) z.2) ∘
      (fun z : X×ℝ => (φ z.1,z.2))) (V×ˢIcc a b)
    exact hc2.comp hmap.continuousOn hmaps
  have hsmg : ∀ p∈V, ∀ x∈Icc a b, ContDiffAt ℝ 2 (g p) x :=
    fun p hp => hsm (φ p) hp
  exact D.eventually_persist_of_eventual_jets (f := g) hV hcg hc2g hsmg hjets

end polyak.ModeLocking.Analysis
