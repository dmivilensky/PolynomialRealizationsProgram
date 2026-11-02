import krylov.Convergence.OneGradientLastCoordinate
import krylov.OneGradient.InformationMoments
import krylov.OneGradient.TrialMinimax

/-!
Article: main_krylov, thm:LB, genuine endpoint selection.
Use: retain the actual common last queried point for every original M1
policy across the whole physical Lanczos fibre, and derive the scalar
endpoint obstruction without assuming positive trials or step independence.
Source: true Krylov information, actual policy causality and the already
proved harmonic two-endpoint minimax theorem.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The genuinely chosen final query depends only on the original
known action, for every span-restricted M1 policy. Article: thm:LB. -/
theorem oneGradientLastQuery_information
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q C : E →L[ℝ] E) (g : E) (N : ℕ)
    (hact : ∀ v∈CG.krylovSpace Q g N,C v=Q v) :
    oneGradientLastQuery m C g N=oneGradientLastQuery m Q g N := by
  unfold oneGradientLastQuery
  rw [one_gradient_information_history m hm Q C g N hact N le_rfl]

/-- All actual physical last-pivot completions share the real last
query, independently of the hidden parameter. Article: thm:LB. -/
theorem oneGradientLastQuery_lanczosCompletion
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) (b : ℝ) :
    oneGradientLastQuery m (cgOperator (lanczosCompletion A hA g hg hc b)) g k=
      oneGradientLastQuery m (cgOperator A) g k :=
  oneGradientLastQuery_information m hm _ _ g k (lanczos_completion_information A hA g hg hc b)

/-- The actual old hidden-coordinate hyperplane is unchanged across
the whole physical fibre, so the genuine cubic prefix theorem applies
at the method-selected endpoint. Article: main_krylov, thm:LB. -/
theorem oneGradient_completion_hidden_zero
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) (b : ℝ) :
    ∀ v∈CG.krylovSpace (cgOperator (lanczosCompletion A hA g hg hc b)) g k,
      inner ℝ (lastLanczosVector A hA g hg hc) v=0 := by
  have hspace := information_krylov_space (cgOperator A)
    (cgOperator (lanczosCompletion A hA g hg hc b)) g k (lanczos_completion_information A hA g hg hc b) k (by omega)
  intro v hv
  rw [hspace] at hv
  exact (krylov_last_lanczos_hyperplane A hA g hg hc v).mp hv

/-- A real common hidden query misses at least one endpoint minimizer
by the original relative minimax amount. Its sign and size are arbitrary;
no trial-positivity or regularity assumption is imposed. Article: thm:LB. -/
theorem oneGradient_endpoint_coordinate_obstruction
    (a b γ p : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃ α∈({a,b} : Set ℝ),intervalMinimaxValue a b*|γ*α|≤|p-γ*α| := by
  by_cases hγ : γ=0
  · refine ⟨a,by simp,?_⟩
    simp only [hγ,zero_mul,abs_zero,mul_zero,sub_zero]
    exact abs_nonneg _
  · have hb := ha.trans_le hab
    have hh := harmonic_trial_lower_bound ha hab (p/γ)
    have hconvert (α : ℝ) (hα : 0<α) :
        |1-(p/γ)/α| *|γ*α|=|p-γ*α| := by
      rw [←abs_mul]
      have he : (1-p/γ/α)*(γ*α)= -(p-γ*α) := by field_simp [hγ,hα.ne'];ring
      rw [he,abs_neg]
    have hchoose : intervalMinimaxValue a b≤|1-(p/γ)/a| ∨
        intervalMinimaxValue a b≤|1-(p/γ)/b| := by
      exact le_max_iff.mp hh
    rcases hchoose with hl|hr
    · refine ⟨a,by simp,?_⟩
      exact (mul_le_mul_of_nonneg_right hl (abs_nonneg _)).trans_eq (hconvert a ha)
    · refine ⟨b,by simp,?_⟩
      exact (mul_le_mul_of_nonneg_right hr (abs_nonneg _)).trans_eq (hconvert b hb)

end
end krylov.Convergence
