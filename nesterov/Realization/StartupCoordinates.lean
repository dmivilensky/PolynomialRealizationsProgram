import nesterov.Realization.Startup
import polyak.Functions.Embedding

/-! The startup witness in the article's literal real Euclidean dimension. -/
noncomputable section
namespace nesterov.Momentum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear isometry transports the actual executor, including its queries. -/
theorem state_embedding (e : E →ₗᵢ[ℝ] F) (g : E→E) (G : F→F)
    (hg : ∀ x,G (e x)=e (g x)) (β τ h : ℝ) (a b : E) (n : ℕ) :
    state G β τ h (e a) (e b) n=
      (e (state g β τ h a b n).1,e (state g β τ h a b n).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [state,ih,step,query]
    have hquery : G (e (state g β τ h a b n).2+
        τ • (e (state g β τ h a b n).2-e (state g β τ h a b n).1))=
        e (g ((state g β τ h a b n).2+τ • ((state g β τ h a b n).2-(state g β τ h a b n).1))) := by
      simpa only [map_add,map_smul,map_sub] using
        hg ((state g β τ h a b n).2+τ • ((state g β τ h a b n).2-(state g β τ h a b n).1))
    rw [hquery]
    simp only [map_sub,map_add,map_smul]

theorem iterate_embedding (e : E →ₗᵢ[ℝ] F) (g : E→E) (G : F→F)
    (hg : ∀ x,G (e x)=e (g x)) (β τ h : ℝ) (x₀ : E) (n : ℕ) :
    iterate G β τ h (e x₀) n=e (iterate g β τ h x₀ n) := by
  exact congrArg Prod.snd (state_embedding e g G hg β τ h x₀ x₀ n)
end nesterov.Momentum

namespace nesterov.Realization
open scoped BigOperators NNReal
open Spectral polyak Filter Set
open scoped Topology
variable (J : Type*) [Fintype J]

/-- The full startup space has exactly `2 card J + 1` real coordinates. -/
def startupCoordinates : WithLp 2 (EuclideanSpace ℂ J×ℝ) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (2*Fintype.card J+1)) := by
  rw [←startup_real_dimension (J:=J)]
  exact (stdOrthonormalBasis ℝ (WithLp 2 (EuclideanSpace ℂ J×ℝ))).repr

variable {J}

/-- The startup construction on literal real Euclidean space, with the entire
physical trajectory transported by one fixed isometry and one fixed objective. -/
theorem exists_real_startup (q : Momentum.Tuning) {μ L t C : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (hfeas : Feasible ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L t)
      t (finiteSpectrum w c hw) C)
    (hstrict : 0<t → |C|<meanG (finiteSpectrum w c hw)
      ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L t)) :
    ∃ lam∈Ioo μ L,∃ Y : ℝ,∃ f : EuclideanSpace ℝ (Fin (2*Fintype.card J+1))→ℝ,
      0<Y ∧ CenteredSmoothStronglyConvex μ L f ∧
      Tendsto (fun n=>Y*Momentum.iterate (fun x : ℝ=>lam*x) q.beta q.tau q.stepSize 1 n) atTop (𝓝 0) ∧
      startupCoordinates J (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0)≠0 ∧
      (∀ n,Momentum.iterate (gradient f) q.beta q.tau q.stepSize
        (startupCoordinates J (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0)) n=
          startupCoordinates J (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y n)) ∧
      ∃ c₀ : ℝ,0<c₀ ∧ ∀ n : ℕ,c₀*Real.exp ((n:ℝ)*t)*
        ‖startupCoordinates J (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0)‖≤
          ‖Momentum.iterate (gradient f) q.beta q.tau q.stepSize
            (startupCoordinates J (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0)) n‖ := by
  obtain ⟨lam,hlam,Y,f,hY,hf,hlim,hx,hr,c₀,hc₀,hbound⟩ :=
    exists_startup q hμ hμL hs w c hw hfeas hstrict
  let e := (startupCoordinates J).toLinearIsometry
  let F := polyak.extendObjective μ L e f
  have hF : CenteredSmoothStronglyConvex μ L F := hf.extendObjective e
  have hgrad : ∀ x,gradient F (e x)=e (gradient f x) :=
    polyak.gradient_extendObjective_embed hf.toSmoothStronglyConvex e
  have he (n : ℕ) := Momentum.iterate_embedding e (gradient f) (gradient F) hgrad
    q.beta q.tau q.stepSize (physical (finiteLatent w c t) q.beta q.tau q.stepSize lam Y 0) n
  refine ⟨lam,hlam,Y,F,hY,hF,hlim,?_,?_,c₀,hc₀,?_⟩
  · exact fun hh=>hx (e.injective (hh.trans e.map_zero.symm))
  · intro n
    exact (he n).trans (congrArg e (hr n))
  · intro n
    change c₀*Real.exp ((n:ℝ)*t)*‖e _‖≤‖Momentum.iterate (gradient F) _ _ _ (e _) n‖
    rw [he,e.norm_map,e.norm_map]
    exact hbound n
end nesterov.Realization
