import krylov.Convergence.ObservableFCPrefix
import krylov.Convergence.ObservableGradientError
import krylov.Correction.SharpRestart
import krylov.Stability.ObservedCanonical
import krylov.Nonlinear.MetricCoordinates

/-!
Article: main_krylov, apG:Dunif, complete observable FC cycle estimate.
Use: bound the actual returned point of the literal first-stopping cycle
from true scalar local data, with no nondegenerate reference or minimum
step assumption. Source: the actual prefix dictionary, genuine staircase
and the proved sharp non-descent restart inequality.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
  krylov.Stability krylov.Correction krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The literal observable FC cycle has a uniform quadratic error bound
for an arbitrary true positive physical reference metric. Every possible
undefined solve, non-descent direction and stationary stop is handled;
all old inverse domains follow from the real pre-stopping observations.
Article: main_krylov, apG:Dunif, FC. -/
theorem observable_fc_actual_cycle_bound
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (r : ℝ) (L : ℝ≥0) (S : ObservableLocalSource (metricCoordinates base hb) f G H r L)
    (m ratio : ℝ) (hm : 0<m) (hratio : 1≤ratio)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hupper : ‖cgOperator base‖≤m^2*ratio^2)
    (bar : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖<r/4)
    (hsmall : (n:ℝ)*(2*(L:ℝ)*‖metricCoordinates base hb x₀‖)≤1/8)
    (hsharp : Real.sqrt n*(4*(L:ℝ)*‖metricCoordinates base hb x₀‖)≤Real.sqrt 3/(8*ratio^2)) :
    ‖metricCoordinates base hb (observableRestartPoint false bar (metricCoordinates base hb) f G r n x₀)‖≤
      256*(L:ℝ)*(1+ratio)*(n:ℝ)*Real.sqrt n*‖metricCoordinates base hb x₀‖^2 := by
  let T := metricCoordinates base hb
  let e := ‖T x₀‖
  let epsilon := 2*(L:ℝ)*e
  have he : 0≤epsilon := by dsimp only [epsilon,e];positivity
  obtain ⟨K,hKn,hout,hgood,hend⟩ := observable_fc_cycle_prefix bar T f G r x₀ n
  let B := observableFCSearchRun T f G r x₀ K
  let g := observableFCCanonicalGradient T f G r x₀ K
  let s := fun i : Fin K=>observableFCCanonicalStep T f G r x₀ i.val
  let y := fun i : Fin K=>observableFCCanonicalGradient T f G r x₀ (i.val+1)-
    observableFCCanonicalGradient T f G r x₀ i.val
  let d := rfcFunctionDirection fullMemory B
  have hKreal : (K:ℝ)≤n := by exact_mod_cast hKn
  have hsmallK : (K:ℝ)*epsilon≤1/8 :=
    (mul_le_mul_of_nonneg_right hKreal he).trans hsmall
  obtain ⟨hgram,hform,hsolve,herror,hres⟩ := S.fc_prefix_bounds x₀ hx₀ K hgood hsmallK
  have hgramhalf : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤1/2 :=
    hgram.trans (hsmallK.trans (by norm_num))
  have hgramspec (i : Fin K) : (3/4:ℝ)≤(crossGram_isHermitian (unitWindow s)).eigenvalues i :=
    (by norm_num : (3/4:ℝ)≤7/8).trans (observable_gram_spectral (unitWindow s) (7/8) hform i)
  have hP := observedProjection_residual_bound (unitWindow s) hgramhalf g
  have hgn : T.symm B.gradient=g := by
    rw [(observableFCSearchRun_semantics T f G r x₀ K).1]
    simp only [g,observableFCCanonicalGradient,coordinateGradient,T.symm_apply_apply]
  have hdir : d=windowDirection (executedPairs (observableFCSearchStep T f G r x₀)
      (observableFCSearchSecant T f G r x₀) K) B.gradient := by
    dsimp only [d,rfcFunctionDirection,B]
    rw [observableFCSearchRun_window]
  have hC : IsUnit (crossGram
      (fun i : Fin K=>observableFCSearchSecant T f G r x₀ i.val)
      (fun i : Fin K=>observableFCSearchStep T f G r x₀ i.val)).det := by
    rw [observableFCSearchRun_window,observable_executed_det_chronological] at hsolve
    exact hsolve
  have hspan : T d+cgOperator base g∈Submodule.span ℝ (Set.range (unitWindow s)) := by
    have hh := chronological_canonical_direction_span base hb (observableFCSearchStep T f G r x₀)
      (observableFCSearchSecant T f G r x₀) B.gradient K
    change T (windowDirection _ B.gradient)+cgOperator base (T.symm B.gradient)∈_ at hh
    rw [←hdir,hgn] at hh
    exact hh
  have hc (i : Fin K) : inner ℝ (unitWindowImages s y i) (T d)=0 := by
    have hh := chronological_canonical_image_conjugacy base hb (observableFCSearchStep T f G r x₀)
      (observableFCSearchSecant T f G r x₀) B.gradient K hC i
    change inner ℝ (T.symm (observableFCSearchSecant T f G r x₀ i.val))
      (T (windowDirection _ B.gradient))=0 at hh
    rw [←hdir] at hh
    have hy : y i=T.symm (observableFCSearchSecant T f G r x₀ i.val) := by
      simp only [y,observableFCCanonicalGradient,coordinateGradient,T.symm_apply_apply,
        observableFCSearchSecant,map_sub]
    change inner ℝ (‖s i‖⁻¹ • y i) (T d)=0
    rw [real_inner_smul_left,hy,hh,mul_zero]
  have hsharpK : Real.sqrt K*(2*epsilon)≤Real.sqrt 3/(8*ratio^2) := by
    have hh := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hKreal) (show 0≤2*epsilon by positivity)
    apply hh.trans
    convert hsharp using 1
    dsimp only [epsilon,e]
    ring
  have hgrad : ‖g‖≤8*(1+ratio)*‖projectedResidual (unitWindow s) g‖ := by
    by_cases hfull : K=n
    · have hd : K=Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simpa using hfull
      have hh := observable_full_residual (unitWindow s) hd (hgram.trans hsmallK) hform g
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : (4:ℝ)≤8*(1+ratio)) (norm_nonneg _))
    · have hbad := hend.resolve_left hfull
      by_cases hz : B.gradient=0
      · have hgzero : g=0 := by rw [←hgn,hz,map_zero]
        rw [hgzero,norm_zero]
        positivity
      · have hslope : 0 ≤ inner ℝ B.gradient d := by
          apply le_of_not_gt
          intro hh
          exact hbad ⟨hz,by
            rw [observableFCSearchRun_window,observable_executed_det_chronological]
            exact hC,hh⟩
        have hpair : inner ℝ g (T d)=inner ℝ B.gradient d := by
          rw [←hgn,real_inner_comm,metric_primal_dual_pairing T S.inverse_symmetric,real_inner_comm]
        have hhy (i : Fin K) : ‖unitWindowImages s y i-unitWindow s i‖≤(2*epsilon)/2 := by
          have hh : ‖unitWindowImages s y i-unitWindow s i‖≤epsilon := herror i
          exact hh.trans_eq (by ring)
        have hh := sharp_observed_nondescent (unitWindow s) (unitWindowImages s y) base hb g (T d)
          m ratio (2*epsilon) hm hratio hlower hupper hgramspec (by positivity) hsharpK hhy hc hspan
          (by rw [hpair];exact hslope)
        exact hh.trans ((mul_le_mul_of_nonneg_left hP (by positivity : 0≤2*(1+ratio))).trans_eq (by ring))
  have hr := S.radius_pos
  have houtball : ‖T (observableFCSearchPoint T f G r x₀ K)‖≤r :=
    (S.fc_localization x₀ (by linarith) K).1.trans (by linarith)
  have hequiv := S.gradient_error (T (observableFCSearchPoint T f G r x₀ K)) houtball
  have hKfactor : (K:ℝ)*Real.sqrt K≤(n:ℝ)*Real.sqrt n :=
    mul_le_mul hKreal (Real.sqrt_le_sqrt hKreal) (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  rw [hout]
  calc
    _ ≤ 2*‖g‖ := hequiv
    _ ≤ 2*(8*(1+ratio)*(16*(L:ℝ)*(K:ℝ)*Real.sqrt K*e^2)) := by
      exact (mul_le_mul_of_nonneg_left hgrad (by norm_num)).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hres (by positivity : 0≤8*(1+ratio))) (by norm_num))
    _ = (256*(L:ℝ)*(1+ratio)*e^2)*((K:ℝ)*Real.sqrt K) := by ring
    _ ≤ (256*(L:ℝ)*(1+ratio)*e^2)*((n:ℝ)*Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hKfactor (by positivity)
    _ = _ := by ring

end
end krylov.Convergence
