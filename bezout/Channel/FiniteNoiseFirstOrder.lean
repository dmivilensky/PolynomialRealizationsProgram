import bezout.Channel.FiniteNoise
import bezout.Gains.Variation

/-!
Article: bezout, Appendix D, the singleton coefficient of the exact finite-noise expansion.
Use: identifies the constructed multilinear coefficient with the actual physical
first variation, hence with the corresponding signal-matrix column.
Proof: restrict the exact expansion to one nonzero call amplitude; uniqueness
of the derivative of the actual causal oracle output identifies its slope.
-/

namespace bezout.Channel
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Restricting to one perturbed call leaves exactly the empty and singleton terms. -/
theorem finiteNoise_single_amplitude (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (s : Fin N) (t : ℝ) :
    finiteNoiseOutput h H P initial (fun j => if j=s.val then t else 0)=
      finiteNoiseCoefficient h H P initial ∅+t • finiteNoiseCoefficient h H P initial {s.val} := by
  rw [finiteNoise_expansion]
  have hs : ({s.val} : Finset ℕ)⊆Finset.range N := by simp
  have hsum := Finset.sum_subset (Finset.powerset_mono.mpr hs)
    (f := fun S : Finset ℕ => (∏ j ∈ S, if j=s.val then t else 0) • finiteNoiseCoefficient h H P initial S)
    (by
      intro S _ hnot
      have hn : ¬S⊆({s.val} : Finset ℕ) := by simpa only [Finset.mem_powerset] using hnot
      obtain ⟨j,hj,hjne⟩ := Finset.not_subset.mp hn
      have hne : j≠s.val := by simpa only [Finset.mem_singleton] using hjne
      have hz : (∏ i ∈ S, if i=s.val then t else 0)=0 :=
        Finset.prod_eq_zero hj (by simp [hne])
      rw [hz, zero_smul])
  rw [← hsum]
  have hsmall := Finset.sum_powerset_insert (a := s.val) (s := ∅)
    (by simp) (fun S => (∏ j ∈ S, if j=s.val then t else 0) • finiteNoiseCoefficient h H P initial S)
  simpa using hsmall

end
end bezout.Channel

namespace bezout.Channel
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every singleton coefficient is the actual physical response to the nominal
query at that same call, for arbitrary deterministic perturbation directions. -/
theorem finiteNoiseCoefficient_singleton (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (s : Fin N) :
    finiteNoiseCoefficient h H P initial {s.val}=
      (aeval H (h.response s)) (P s ((aeval H (h.query s)) initial)) := by
  let D : Fin N → E →ₗ[ℝ] E := fun j => if j=s then P s else 0
  have hf : (fun t => h.oracleOutput initial (bezout.History.perturbedOracle H D t))=
      (fun t => finiteNoiseOutput h H P initial (fun j => if j=s.val then t else 0)) := by
    funext t
    congr 1
    funext j v
    by_cases hj : j=s
    · subst j
      simp [bezout.History.perturbedOracle, D]
    · have hval : j.val≠s.val := fun hval => hj (Fin.ext hval)
      simp [bezout.History.perturbedOracle, D, hj, hval]
  have hd : HasDerivAt
      (fun t => finiteNoiseOutput h H P initial (fun j => if j=s.val then t else 0))
      (finiteNoiseCoefficient h H P initial {s.val}) 0 := by
    have hh := (hasDerivAt_const (0:ℝ) (finiteNoiseCoefficient h H P initial ∅)).add
      ((hasDerivAt_id (0:ℝ)).smul_const (finiteNoiseCoefficient h H P initial {s.val}))
    convert hh using 1
    · funext t
      exact finiteNoise_single_amplitude h H P initial s t
    · simp
  have hp := h.hasDerivAt_perturbed_output H D initial
  rw [hf] at hp
  have he := hd.unique hp
  rw [he]
  unfold bezout.History.firstVariation bezout.History.variationNoise
  calc
    _ = ∑ j : Fin N, if j=s then
        (aeval H (h.response s)) (P s ((aeval H (h.query s)) initial)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j=s
      · subst j; simp [D]
      · simp [D, hj]
    _ = _ := by simp

end
end bezout.Channel
