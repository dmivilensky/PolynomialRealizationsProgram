import polyak.General.IQC.WeightedShift
import polyak.Growth.Plateau
import polyak.Growth.OriginalRate

/-! Appendix D, the passage from a uniform energy estimate at ONE exponent
to the strict original rate. Restarting an actual trajectory is essential:
the constants quantify over every potential, dimension and initial pair. -/
noncomputable section
namespace polyak.General.IQC
open polyak Growth Finset

def UniformMassBound (A B β t C : ℝ) : Prop :=
  ∀ d : ℕ,∀ r : Run (EuclideanSpace ℝ (Fin d)) A B β,∀ n : ℕ,
    mass (discountedEnergy r.x t) 0 n≤C*stateNorm r.x 0^2

theorem discountedEnergy_mono_exponent {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) {t s : ℝ} (hts : t≤s) (k : ℕ) :
    discountedEnergy x s k≤discountedEnergy x t k := by
  unfold discountedEnergy
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hk : 0≤(k : ℝ):=Nat.cast_nonneg k
  nlinarith

theorem uniformMassBound_mono_exponent {A B β t s C : ℝ} (hts : t≤s)
    (hbound : UniformMassBound A B β t C) : UniformMassBound A B β s C := by
  intro d r n
  apply le_trans _ (hbound d r n)
  exact sum_le_sum (fun k _ => discountedEnergy_mono_exponent r.x hts k)

theorem uniformMassBound_tails {A B β t C : ℝ} (hC : 0<C)
    (hbound : UniformMassBound A B β t C) :
    ∃ D : ℝ,1<D ∧ ∀ d : ℕ,∀ r : Run (EuclideanSpace ℝ (Fin d)) A B β,
      ∀ i j : ℕ,i≤j → mass (discountedEnergy r.x t) i j≤
        D*(discountedEnergy r.x t i+discountedEnergy r.x t (i+1)) := by
  let D:=2+C*(1+Real.exp (2*t))
  have hD : 1<D:=by dsimp [D]; nlinarith [Real.exp_pos (2*t)]
  refine ⟨D,hD,fun d r i j hij => ?_⟩
  have hh:=hbound d (r.shift i) (j-i)
  have he : mass (discountedEnergy (r.shift i).x t) 0 (j-i)=
      Real.exp (2*i*t)*mass (discountedEnergy r.x t) i j:=by
    change mass (discountedEnergy (fun k => r.x (i+k)) t) 0 (j-i)=_
    rw [mass_discountedEnergy_shift,Nat.add_sub_of_le hij]
  rw [he] at hh
  have hc : Real.exp (-2*i*t)*Real.exp (2*i*t)=1:=by
    rw [←Real.exp_add,show -2*(i : ℝ)*t+2*i*t=0 by ring,Real.exp_zero]
  have hm:=mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*i*t)).le
  rw [←mul_assoc,hc,one_mul] at hm
  have hs : Real.exp (-2*i*t)*stateNorm (r.shift i).x 0^2=
      discountedEnergy r.x t i+Real.exp (2*t)*discountedEnergy r.x t (i+1):=by
    change Real.exp (-2*i*t)*stateNorm r.x i^2=_
    exact discounted_stateNorm r.x t i
  have heq : Real.exp (-2*i*t)*(C*stateNorm (r.shift i).x 0^2)=
      C*(discountedEnergy r.x t i+Real.exp (2*t)*discountedEnergy r.x t (i+1)):=by
    rw [←mul_assoc,mul_comm (Real.exp _) C,mul_assoc,hs]
  rw [heq] at hm
  have h0:=discountedEnergy_nonneg r.x t i
  have h1:=discountedEnergy_nonneg r.x t (i+1)
  apply hm.trans
  dsimp [D]
  nlinarith [Real.exp_pos (2*t),mul_nonneg hC.le h0,
    mul_nonneg (mul_nonneg hC.le (Real.exp_pos (2*t)).le) h0]

theorem growthRate_lt_exp_of_uniformMassBound {A B β t C : ℝ}
    (hB : B≠0) (hC : 0<C) (hbound : UniformMassBound A B β t C) :
    growthRate A B β<Real.exp t := by
  by_contra hn
  have hts : t≤Real.log (growthRate A B β):=by
    rw [←Real.exp_le_exp,Real.exp_log (growthRate_pos A B β)]
    exact le_of_not_gt hn
  obtain ⟨D,hD,htails⟩:=uniformMassBound_tails hC
    (uniformMassBound_mono_exponent hts hbound)
  exact not_uniform_mass_bound hB hD htails

theorem originalRate_lt_exp_of_uniformMassBound {μ L α β t C : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hC : 0<C)
    (hbound : UniformMassBound (Dynamics.normalizedA μ L α β)
      (Dynamics.normalizedB μ L α) β t C) : Dynamics.rate μ L α β<Real.exp t := by
  have hB : Dynamics.normalizedB μ L α≠0:=by
    dsimp [Dynamics.normalizedB]
    positivity
  exact (originalRate_le_growthRate hμ hL hα hβ).trans_lt
    (growthRate_lt_exp_of_uniformMassBound hB hC hbound)

end polyak.General.IQC
