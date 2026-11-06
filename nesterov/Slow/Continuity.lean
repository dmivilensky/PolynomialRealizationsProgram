import nesterov.Slow.Model
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Finite-degree coefficient continuity, including monic synthetic division.
The degree bound is fixed, but the actual degree may drop at the limit. -/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set
open scoped Topology

lemma coeff_divByMonic_bounded (p : Polynomial ℝ) (a : ℝ) {N : ℕ}
    (hN : p.natDegree≤N) (n : ℕ) :
    (p /ₘ (X-C a)).coeff n=∑ i∈Finset.Icc (n+1) N,a^(i-(n+1))*p.coeff i := by
  rw [coeff_divByMonic_X_sub_C]
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN)
  intro i hi hnot
  have hgt : p.natDegree < i := by
    have hlo := (Finset.mem_Icc.mp hi).1
    exact lt_of_not_ge (fun hh=>hnot (Finset.mem_Icc.mpr ⟨hlo,hh⟩))
  rw [coeff_eq_zero_of_natDegree_lt hgt,mul_zero]

lemma tendsto_divByMonic_coeff {A : Type*} {l : Filter A} {p : A→Polynomial ℝ}
    {p₀ : Polynomial ℝ} {a : A→ℝ} {a₀ : ℝ} {N : ℕ}
    (hp : ∀ j,Tendsto (fun e=>(p e).coeff j) l (𝓝 (p₀.coeff j)))
    (hdeg : ∀ e,(p e).natDegree≤N) (hdeg₀ : p₀.natDegree≤N)
    (ha : Tendsto a l (𝓝 a₀)) (n : ℕ) :
    Tendsto (fun e=>(p e /ₘ (X-C (a e))).coeff n) l (𝓝 ((p₀ /ₘ (X-C a₀)).coeff n)) := by
  simp_rw [coeff_divByMonic_bounded _ _ (hdeg _) n,coeff_divByMonic_bounded _ _ hdeg₀ n]
  exact tendsto_finsetSum _ (fun i _=>(ha.pow _).mul (hp i))

lemma tendsto_eval₂_of_coeff {A : Type*} {l : Filter A} {p : A→Polynomial ℝ}
    {p₀ : Polynomial ℝ} {z : A→ℂ} {z₀ : ℂ} {N : ℕ}
    (hp : ∀ j,Tendsto (fun e=>(p e).coeff j) l (𝓝 (p₀.coeff j)))
    (hdeg : ∀ e,(p e).natDegree<N) (hdeg₀ : p₀.natDegree<N)
    (hz : Tendsto z l (𝓝 z₀)) :
    Tendsto (fun e=>(p e).eval₂ Complex.ofRealHom (z e)) l (𝓝 (p₀.eval₂ Complex.ofRealHom z₀)) := by
  simp_rw [eval₂_eq_sum_range' Complex.ofRealHom (hdeg _) _,eval₂_eq_sum_range' Complex.ofRealHom hdeg₀ _]
  exact tendsto_finsetSum _ (fun j _=>
    ((Complex.continuous_ofReal.tendsto _).comp (hp j)).mul (hz.pow j))

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

theorem u_coeff_tendsto (j : ℕ) : Tendsto (fun ε=>(F.u ε).coeff j) (𝓝[>] (0:ℝ)) (𝓝 ((F.u 0).coeff j)) :=
  (F.query_cont j).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

theorem v_coeff_tendsto (j : ℕ) : Tendsto (fun ε=>(F.v ε).coeff j) (𝓝[>] (0:ℝ)) (𝓝 ((F.v 0).coeff j)) :=
  (F.recurrence_cont j).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

theorem u_eval_tendsto {z : ℝ→ℂ} {z₀ : ℂ} (hz : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 z₀)) :
    Tendsto (fun ε=>(F.u ε).eval₂ Complex.ofRealHom (z ε)) (𝓝[>] (0:ℝ))
      (𝓝 ((F.u 0).eval₂ Complex.ofRealHom z₀)) :=
  tendsto_eval₂_of_coeff F.u_coeff_tendsto F.u_natDegree_lt (F.u_natDegree_lt 0) hz

theorem v_eval_tendsto {z : ℝ→ℂ} {z₀ : ℂ} (hz : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 z₀)) :
    Tendsto (fun ε=>(F.v ε).eval₂ Complex.ofRealHom (z ε)) (𝓝[>] (0:ℝ))
      (𝓝 ((F.v 0).eval₂ Complex.ofRealHom z₀)) :=
  tendsto_eval₂_of_coeff (N:=F.memory+1) F.v_coeff_tendsto (fun ε=>by rw [F.v_natDegree];omega)
    (by rw [F.v_natDegree];omega) hz

end SecondOrderFamily
end
end nesterov.Slow
