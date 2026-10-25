import polyak.General.Regions.Periodic
import polyak.General.Regions.PhaseLocking
import polyak.General.RootsOriginal

/-! Source Theorem A in arbitrary original curvature and step units.
Scaling transports the single objective and the entire executed trajectory,
not merely its asymptotic scalar rate. -/
noncomputable section
namespace polyak.General.Regions
open Dynamics Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_mul (f : E → ℝ) (hf : Differentiable ℝ f) (c : ℝ) :
    gradient (fun x => c*f x)=fun x => c • gradient f x := by
  apply gradient_eq
  intro x
  simpa using hasGradientAt_quadratic_add (hf x).hasGradientAt 0 c

theorem centered_mul {μ L c : ℝ} {f : E → ℝ}
    (hf : CenteredSmoothStronglyConvex μ L f) (hc : 0<c) :
    CenteredSmoothStronglyConvex (c*μ) (c*L) (fun x => c*f x) := by
  refine ⟨hf.toSmoothStronglyConvex.mul_pos hc,by simp [hf.value_zero],?_⟩
  simp only [gradient_mul f hf.differentiable c,hf.gradient_zero,smul_zero]

theorem original_omegaOne_converges {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β))
    (hq : OmegaOne (Tuning.ofOriginal μ L α β hμ hL hα hβ hβ1 hquad))
    {f : E → ℝ} (hf : SmoothStronglyConvex μ L f)
    (a : E) (hmin : ∀ y,f a≤f y) (x₀ : E) :
    Tendsto (iterate (gradient f) α β x₀) atTop (𝓝 a) := by
  let q:=Tuning.ofOriginal μ L α β hμ hL hα hβ hβ1 hquad
  have hfs : SmoothStronglyConvex q.x q.y (fun x => α*f x):=by
    change SmoothStronglyConvex
      (Tuning.ofOriginal μ L α β hμ hL hα hβ hβ1 hquad).x (α*L) (fun x => α*f x)
    rw [Tuning.ofOriginal_x]
    exact hf.mul_pos hα
  have hh:=omegaOne_converges q hq hfs a
    (fun y => mul_le_mul_of_nonneg_left (hmin y) hα.le) x₀
  have he : (fun n => iterate (gradient (fun x => α*f x)) 1 β x₀ n)=
      iterate (gradient f) α β x₀:=by
    funext n
    rw [gradient_mul f hf.differentiable α]
    simpa only [div_self (ne_of_gt hα)] using
      iterate_scale_gradient (gradient f) α β α (ne_of_gt hα) x₀ n
  exact he ▸ hh

theorem original_exists_periodic_orbit {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β))
    {j k : ℕ} (hcop : j.Coprime k) (hj : 1≤j) (hjk : 2*j<k)
    (hphase : (Tuning.ofOriginal μ L α β hμ hL hα hβ hβ1 hquad).angle
      (rationalAngle j k)≤Real.pi/k) :
    ∃ f : EuclideanSpace ℝ (Fin 3)→ℝ,
      CenteredSmoothStronglyConvex μ L f ∧ ∃ x₀,x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧
      ∃ J : EuclideanSpace ℂ (Fin 1)→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∃ orbit : ℕ→EuclideanSpace ℝ (Fin 3),Function.Periodic orbit k ∧
        (∀ n,orbit n=J (Waves.finitePosition (fun _ : Fin 1=>1)
          (fun _=>cosineFrequency (rationalAngle j k)) 0 (some n))) ∧
        (∀ n,c₀*‖x₀‖≤‖iterate (gradient f) α β x₀ n‖) ∧
        Tendsto (fun n=>iterate (gradient f) α β x₀ n-orbit n) atTop (𝓝 0) := by
  let q:=Tuning.ofOriginal μ L α β hμ hL hα hβ hβ1 hquad
  obtain ⟨F,hF,x₀,hx,c₀,hc,J,orbit,hper,hmodel,hbound,hlim⟩:=
    exists_periodic_orbit q hcop hj hjk hphase
  let f:=fun x => (1/α)*F x
  have hf : CenteredSmoothStronglyConvex μ L f:=by
    have hh:=centered_mul hF (one_div_pos.mpr hα)
    have heμ : (1/α)*q.x=μ:=by rw [Tuning.ofOriginal_x]; field_simp
    have heL : (1/α)*q.y=L:=by change (1/α)*(α*L)=L; field_simp
    simpa only [heμ,heL] using hh
  have he (n : ℕ) : iterate (gradient f) α β x₀ n=iterate (gradient F) 1 q.beta x₀ n:=by
    change iterate (gradient f) α β x₀ n=iterate (gradient F) 1 β x₀ n
    rw [gradient_mul F hF.differentiable (1/α)]
    have hh:=iterate_scale_gradient (gradient F) 1 β (1/α) (one_div_ne_zero (ne_of_gt hα)) x₀ n
    simpa only [one_div_one_div] using hh
  refine ⟨f,hf,x₀,hx,c₀,hc,J,orbit,hper,hmodel,?_,?_⟩
  · intro n
    rw [he]
    exact hbound n
  · simpa only [he] using hlim

end polyak.General.Regions
