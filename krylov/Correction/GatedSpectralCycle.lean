import krylov.Correction.GatedUniformBounds

/-!
Article: main_krylov, thm:UCg(i,ii), original spectral-interval quantifiers.
Use: Place the actual gated cycle bounds over every positive interval [mu,L]
and the original dimension-times-increment allowance with one common constant.
Source: proved whole-class actual gated bounds and the Hermitian spectral
norm characterization; no compactness of the active CG stratum is used.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- Both actual gated-RFC metric estimates are uniform on the entire original spectral class.
Use: Pass from the true operator budget to the original increment-size parameter.
Article: main_krylov, thm:UCg(i,ii).
Proof: The interval hypothesis bounds the genuine base operator norm by kappa times its positive lower endpoint. Apply the completed actual operator-cycle theorem with budget (n+1) omega, and enlarge the common constant by (n+1)^3. This includes zero budgets and the actual last-query condition.
-/
theorem gated_uniform_spectral_cycle (n : ℕ) (hn : 2≤n) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ω : ℝ), 0≤ω → ω≤ω₀ → gatedFullRunDefined γ A B g n →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤((n : ℝ)+1)*ω) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤((n : ℝ)+1)*ω) →
      let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
      let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      ‖J (probedGradient m A B g n)‖≤C*ω^2*‖J g‖ ∧
        ((probedPhase m A B g (n-1)).trace≠[] →
          ‖J (probedGradient m A B g n)‖≤C*(ω^2*‖J (probedGradient m A B g (n-1))‖+ω^3*‖J g‖)) := by
  obtain ⟨δ,C₀,hδ,hC₀,hbound⟩ := gated_uniform_cycle n hn κ γ hκ hγ hγ1
  let D := (n : ℝ)+1
  let C := C₀*D^3
  have hD : 0<D := by dsimp only [D]; positivity
  have hD1 : 1≤D := by dsimp only [D]; have hn0 := Nat.cast_nonneg (α := ℝ) n; linarith
  have hD23 : D^2≤D^3 := by nlinarith [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hD1)]
  refine ⟨δ/D,C,div_pos hδ hD,mul_pos hC₀ (pow_pos hD 3),?_⟩
  intro base hb μ L hμ hratio hspec A B g ω hω he hdefined hA hB
  have hL : 0≤L := hμ.le.trans ((hspec ⟨0,by omega⟩).1.trans (hspec ⟨0,by omega⟩).2)
  have hnorm := (cgOperator_norm_le base hb hL (fun i => (hspec i).2)).trans ((div_le_iff₀ hμ).mp hratio)
  have hε : 0≤D*ω := mul_nonneg hD.le hω
  have heδ : D*ω≤δ := by have ht := (le_div_iff₀ hD).mp he; nlinarith
  have hb' := hbound base hb μ hμ (fun i => (hspec i).1) hnorm A B g (D*ω) hε heδ hdefined hA hB
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  dsimp only
  refine ⟨?_,?_⟩
  · have hcoef := mul_le_mul_of_nonneg_left hD23 hC₀.le
    calc
      _ ≤ (C₀*D^2)*(ω^2*‖J g‖) := hb'.1.trans_eq (by ring)
      _ ≤ (C₀*D^3)*(ω^2*‖J g‖) := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by dsimp only [C]; ring
  · intro htrace
    have ht := hb'.2 htrace
    have h₁ := mul_le_mul_of_nonneg_right hD23 (mul_nonneg (sq_nonneg ω) (norm_nonneg (J (probedGradient m A B g (n-1)))))
    calc
      _ ≤ C₀*(D^2*(ω^2*‖J (probedGradient m A B g (n-1))‖)+D^3*(ω^3*‖J g‖)) := ht.trans_eq (by ring)
      _ ≤ C₀*(D^3*(ω^2*‖J (probedGradient m A B g (n-1))‖)+D^3*(ω^3*‖J g‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add h₁ (le_refl _)) hC₀.le
      _ = _ := by dsimp only [C]; ring

end
end krylov.Correction
