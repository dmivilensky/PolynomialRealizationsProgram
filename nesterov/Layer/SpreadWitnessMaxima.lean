import nesterov.Layer.SpreadWitness
import Mathlib.Topology.Order.Compact

/-! The literal source maxima over the moving band, with attained maxima
proved from compactness and continuity rather than assumed. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Spectral Phase Asymptotics
open scoped Topology BigOperators NNReal

namespace Spread

def bandMaximum (f : ℝ→ℝ) (s : ℝ) (K : ℕ) : ℝ :=
  sSup (f '' band s (nesterov.Spread.centerAngle K))

theorem bandMaximum_isGreatest {f : ℝ→ℝ} (hf : Continuous f) {s : ℝ} {K : ℕ}
    (hs : 0≤s) (hK : 3≤K) :
    IsGreatest (f '' band s (nesterov.Spread.centerAngle K)) (bandMaximum f s K) := by
  have hω := nesterov.Spread.centerAngle_pos hK
  have hne : (band s (nesterov.Spread.centerAngle K)).Nonempty := by
    refine ⟨nesterov.Spread.centerAngle K,?_,?_⟩ <;> nlinarith [mul_nonneg hs hω.le]
  exact ((isCompact_Icc : IsCompact (band s (nesterov.Spread.centerAngle K))).image hf).isGreatest_sSup
    (hne.image f)

theorem le_bandMaximum {f : ℝ→ℝ} (hf : Continuous f) {s ω : ℝ} {K : ℕ}
    (hs : 0≤s) (hK : 3≤K) (hω : ω∈band s (nesterov.Spread.centerAngle K)) :
    f ω≤bandMaximum f s K := (bandMaximum_isGreatest hf hs hK).2 ⟨ω,hω,rfl⟩

theorem exists_bandMaximum {f : ℝ→ℝ} (hf : Continuous f) {s : ℝ} {K : ℕ}
    (hs : 0≤s) (hK : 3≤K) :
    ∃ ω∈band s (nesterov.Spread.centerAngle K),f ω=bandMaximum f s K :=
  (bandMaximum_isGreatest hf hs hK).1

theorem continuous_abs_mixed (q : Momentum.Tuning) (μ L r : ℝ) :
    Continuous (fun ω=>|mixedPolynomial q.beta q.tau (q.stepSize*μ) (q.stepSize*L)
      r (1-Real.cos ω)|) := by
  have he : (fun ω=>|mixedPolynomial q.beta q.tau (q.stepSize*μ) (q.stepSize*L)
      r (1-Real.cos ω)|)=(fun ω=>|mixedQ0 q.beta q.tau (q.stepSize*μ) (q.stepSize*L) r+
        mixedQ1 q.beta q.tau (q.stepSize*μ) (q.stepSize*L) r*(1-Real.cos ω)+
        mixedQ2 q.beta q.tau (q.stepSize*μ) (q.stepSize*L) r*(1-Real.cos ω)^2|) := by
    funext ω
    rw [mixedPolynomial_coefficients]
  rw [he]
  fun_prop

theorem continuous_norm_product (q : Momentum.Tuning) (μ L r : ℝ) :
    Continuous (fun ω=>‖product q μ L r ω‖) := by
  unfold product Quadratic.characteristic Quadratic.queryPolynomial circle polyak.Waves.z
  fun_prop

theorem littleO_rpow_iff_cubic_ratio {A : Type*} {l : Filter A} {f x : A→ℝ}
    (hx : ∀ᶠ a in l,0<x a) :
    f =o[l] (fun a=>(x a)^(3/2:ℝ)) ↔
      Tendsto (fun a=>f a/cubicScale (x a)) l (𝓝 0) := by
  have hz : ∀ᶠ a in l,(x a)^(3/2:ℝ)=0 → f a=0 := by
    filter_upwards [hx] with a ha hzero
    exact False.elim ((Real.rpow_pos_of_pos ha (3/2:ℝ)).ne' hzero)
  rw [isLittleO_iff_tendsto' hz]
  have heq : (fun a=>f a/(x a)^(3/2:ℝ))=ᶠ[l] (fun a=>f a/cubicScale (x a)) := by
    filter_upwards [hx] with a ha
    rw [cubicScale_eq_rpow ha]
  exact ⟨fun h=>h.congr' heq,fun h=>h.congr' heq.symm⟩

end Spread

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def spreadMixedMaximum (c s : ℝ) (K : A→ℕ) (a : A) : ℝ :=
  Spread.bandMaximum (fun ω=>|mixedPolynomial (F.tuning a).beta (F.tuning a).tau
    ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
    (1-c*F.epsilon a) (1-Real.cos ω)|) s (K a)

def spreadProductMaximum (c s : ℝ) (K : A→ℕ) (a : A) : ℝ :=
  Spread.bandMaximum (fun ω=>‖Spread.product (F.tuning a) (F.epsilon a^2) 1
    (1-c*F.epsilon a) ω‖) s (K a)

/-- Lemma spreadwit with the article's actual maxima and literal little-o
hypotheses. Maximal values and the finite real realization are proved. -/
theorem spread_witness_from_maxima {c s lam : ℝ} {K : A→ℕ}
    (hc0 : 0<c) (hc : c<θ/2) (hτ : 0<τ)
    (hs0 : 0<s) (hs1 : s≤nesterov.Spread.canonicalKernel.s1) (hlam : 0<lam)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hK : ∀ᶠ a in l,3≤K a)
    (hH : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      ((1-circle (1-c*F.epsilon a) ω)*
        Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω).re≤
          -lam*F.epsilon a*F.spreadProductMaximum c s K a)
    (hεscale : F.epsilon =o[l] (fun a=>
      (Spread.xiMax s (nesterov.Spread.centerAngle (K a)))^(3/2:ℝ)))
    (hMscale : F.spreadMixedMaximum c s K =o[l] (fun a=>
      (Spread.xiMax s (nesterov.Spread.centerAngle (K a)))^(3/2:ℝ))) :
    ∀ᶠ a in l,∃ (J : Type) (_ : Fintype J) (w : J→ℝ≥0) (q : J→Frequency)
      (hw : ∑ j,w j=1),
      (∀ j,Real.arccos (q j:ℝ)∈Spread.sourceBand (K a) s) ∧
      ∃ C : ℝ,Feasible (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a))
        (Real.log (1-c*F.epsilon a)) (finiteSpectrum w q hw) C ∧
      |C|<meanG (finiteSpectrum w q hw)
        (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a)) ∧
      RestLowerWitness (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) (2*Fintype.card J+1) ∧
      1-c*F.epsilon a≤Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  have hs6 : s∈Ioc (0:ℝ) (1/6) :=
    ⟨hs0,hs1.trans nesterov.Spread.canonicalKernel.s1_le_one_sixth⟩
  have hxi : ∀ᶠ a in l,0<Spread.xiMax s (nesterov.Spread.centerAngle (K a)) := by
    filter_upwards [hK] with a ha
    exact Spread.xiMax_pos hs6 ⟨nesterov.Spread.centerAngle_pos ha,nesterov.Spread.centerAngle_le ha⟩
  apply F.spread_witness (M:=F.spreadMixedMaximum c s K)
    (X:=F.spreadProductMaximum c s K) hc0 hc hτ hs0 hs1 hlam hstable hK ?_ ?_ hH
    ((Spread.littleO_rpow_iff_cubic_ratio hxi).mp hεscale)
    ((Spread.littleO_rpow_iff_cubic_ratio hxi).mp hMscale)
  · filter_upwards [hK] with a ha ω hω
    simpa only [spreadMixedMaximum,mul_one] using
      Spread.le_bandMaximum (Spread.continuous_abs_mixed (F.tuning a) (F.epsilon a^2) 1
        (1-c*F.epsilon a)) hs0.le ha hω
  · filter_upwards [hK] with a ha ω hω
    exact Spread.le_bandMaximum (Spread.continuous_norm_product (F.tuning a) (F.epsilon a^2) 1
      (1-c*F.epsilon a)) hs0.le ha hω

end Scaling
end
end nesterov.TwoStep
