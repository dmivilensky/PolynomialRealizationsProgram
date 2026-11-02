import krylov.XR.LocalReferenceChart
import krylov.XR.XRFCScalarDictionary

/-!
Article: main_krylov, lem:xr-local, smoothness of the actual trial vector.
Use: the primitive endpoint trial hypotheses imply C² regularity of the
finite vector of actually computed trials as a function of its genuine
finite response transcript. No output smoothness or trial-drift bound is
assumed. The exact executor dictionary identifies this vector on real data.
Source: finite causal endpoint program and composition of actual C² maps.
-/
namespace krylov.XR
noncomputable section
open Matrix Filter Topology krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Restriction of a real adaptive transcript is its earlier transcript. -/
theorem adaptiveTranscript_castLE {D : Type*}
    (query : (k : ℕ) → (Fin k → D) → E) (oracle : E → D)
    (N k : ℕ) (hk : k ≤ N) :
    (fun i : Fin k => adaptiveTranscript query oracle N (Fin.castLE hk i)) =
      adaptiveTranscript query oracle k := by
  induction N with
  | zero =>
    have h : k = 0 := by omega
    subst k
    rfl
  | succ N ih =>
    by_cases h : k = N+1
    · subst k; rfl
    · have hkn : k ≤ N := by omega
      funext i
      have he : Fin.castLE hk i = (Fin.castLE hkn i).castSucc := by ext; rfl
      rw [adaptiveTranscript, he, Fin.snoc_castSucc]
      exact congrFun (ih hkn) i

/-- The actual causal trial vector, read from one complete endpoint-data
transcript; only the observations preceding each trial are used. -/
def endpointProgramTrialVector (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (x₀ : E) (f₀ : ℝ) (g₀ : E)
    (N : ℕ) (data : Fin N → ℝ × E) : Fin N → ℝ :=
  fun k => trial k.val (endpointProgramChart values trial x₀ f₀ g₀ k.val
    (fun i => data (Fin.castLE k.isLt.le i)))

/-- Primitive smoothness at the true reference prefixes derives smoothness
of the actual computed vector, with no executed-output regularity premise. -/
theorem endpointProgramTrialVector_contDiffAt (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (x₀ : E) (f₀ : ℝ) (g₀ : E)
    (N : ℕ) (reference : E → ℝ × E) (r : WithTop ℕ∞)
    (hdomains : ∀ k < N, EndpointProgramDomain values trial x₀ f₀ g₀ r k
      (adaptiveTranscript (endpointProgramQuery values trial x₀ f₀ g₀) reference k)) :
    ContDiffAt ℝ r (endpointProgramTrialVector values trial x₀ f₀ g₀ N)
      (adaptiveTranscript (endpointProgramQuery values trial x₀ f₀ g₀) reference N) := by
  apply contDiffAt_pi.mpr
  intro k
  let data := adaptiveTranscript (endpointProgramQuery values trial x₀ f₀ g₀) reference N
  let takeData := fun d : Fin N → ℝ × E => fun i : Fin k.val => d (Fin.castLE k.isLt.le i)
  have hp : ContDiffAt ℝ r takeData data := by
    apply contDiffAt_pi.mpr
    intro i
    exact contDiffAt_apply ℝ (ℝ × E) (Fin.castLE k.isLt.le i) data
  have he : takeData data = adaptiveTranscript
      (endpointProgramQuery values trial x₀ f₀ g₀) reference k.val :=
    adaptiveTranscript_castLE _ _ _ _ k.isLt.le
  have hd := hdomains k.val k.isLt
  have hc := (endpointProgram_contDiff values trial x₀ f₀ g₀ r k.val _ hd).1
  have ht := (EndpointProgramDomain.current values trial x₀ f₀ g₀ r k.val _ hd).1
  rw [←he] at hc ht
  exact ht.comp data (hc.comp data hp)

/-- At actual function observations, the smooth transcript vector is
exactly the vector used by the genuine native full-memory execution. -/
theorem endpointProgramTrialVector_actual (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n+1) (hmax : P.maximumCapacity = n+1)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (x₀ : EuclideanSpace ℝ (Fin (n+1))) (N : ℕ) (hN : N ≤ n+1) :
    endpointProgramTrialVector P.valuesEnabled (endpointComputedTrial P bounds) x₀ (f x₀) (G x₀) N
      (adaptiveTranscript (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds)
        x₀ (f x₀) (G x₀)) (fun x => (f x, G x)) N) =
      fullVirtualTrialVector P f G x₀ bounds N := by
  funext k
  unfold endpointProgramTrialVector fullVirtualTrialVector
  rw [adaptiveTranscript_castLE, ← endpointFunctionRun_eq_program]
  exact (fullVirtualRun_trial_endpoint P bounds hinit hmax f G x₀ k.val
    (k.isLt.le.trans hN)).symm

/-- For the native rule itself, the original positive C² endpoint-trial
hypotheses and full-atom quadratic data derive C² of its complete finite
trial vector. Every solve domain is proved rather than assumed. -/
theorem nativeTrialVector_contDiffAt (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C) :
    ContDiffAt ℝ 2
      (endpointProgramTrialVector P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀ n)
      (adaptiveTranscript (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds)
        0 constant g₀) (fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) n) := by
  exact endpointProgramTrialVector_contDiffAt _ _ _ _ _ _ _ _
    (quadratic_endpointProgram_domains P bounds hinit hmax Q hQ hpos g₀ constant hg htrial)

end
end krylov.XR
