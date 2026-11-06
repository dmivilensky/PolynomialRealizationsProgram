import nesterov.Layer.SpreadWitness

/-! Fixed rational bands are a special case of the moving-band spread theorem.
The resulting objective and rest start precede all execution horizons. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set Spectral Phase
open scoped Topology BigOperators NNReal

variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem fixed_band_rest_witness {c s lam M X : ℝ} {K : ℕ}
    (hc0 : 0<c) (hc : c<θ/2) (hτ : 0<τ)
    (hs0 : 0<s) (hs1 : s≤nesterov.Spread.canonicalKernel.s1) (hlam : 0<lam)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) (hK : 3≤K)
    (hM : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle K),
      |mixedPolynomial (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-c*F.epsilon a) (1-Real.cos ω)|≤M*F.epsilon a)
    (hX : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle K),
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤X)
    (hH : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle K),
      ((1-circle (1-c*F.epsilon a) ω)*
        Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω).re≤
          -lam*F.epsilon a*X) :
    ∀ᶠ a in l,∃ d : ℕ,
      RestLowerWitness (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) d ∧
      1-c*F.epsilon a≤Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  have hz := F.epsilon_zero.div_const
    (Spread.cubicScale (Spread.xiMax s (nesterov.Spread.centerAngle K)))
  have hMz := (F.epsilon_zero.const_mul M).div_const
    (Spread.cubicScale (Spread.xiMax s (nesterov.Spread.centerAngle K)))
  simp only [zero_div,mul_zero] at hz hMz
  have h := F.spread_witness (K:=fun _=>K) (M:=fun a=>M*F.epsilon a) (X:=fun _=>X)
    hc0 hc hτ hs0 hs1 hlam hstable (Eventually.of_forall fun _=>hK) hM hX hH hz hMz
  filter_upwards [h] with a ha
  rcases ha with ⟨J,inst,w,q,hw,hband,C,hfeas,hreserve,hwitness,hrate⟩
  let : Fintype J := inst
  exact ⟨2*Fintype.card J+1,hwitness,hrate⟩

end
end nesterov.TwoStep.Scaling
