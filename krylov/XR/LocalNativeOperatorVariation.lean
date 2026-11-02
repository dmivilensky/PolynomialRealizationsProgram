import krylov.XR.LocalOperatorOutputDictionary
import krylov.Convergence.VirtualDerivativeCoordinates
import krylov.Envelope.XRFCOutputJet

/-!
Article: main_krylov, lem:xr-local, assembled native I/E1 first variation.
Use: the actual operator-input native trial vector has the same complete
point/semantic-gradient first variation as its fixed reference vector, at
every prefix. The C² trial regularity and O(E²) comparison are derived
from the original endpoint primitives, never assumed as output fields.
Source: finite native operator induction and genuine joint XRFC calculus.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability Filter Topology Asymptotics
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Actual native finite point and semantic-gradient response. Its trial
vector is computed recursively by the native rule from observed inputs. -/
def nativeOperatorOutput (P : Parameters) (bounds : SpectralBounds)
    (Q : E →L[ℝ] E) (g : E) (constant : ℝ) (N : ℕ)
    (e : Fin (N+1) → E →L[ℝ] E) : E × E :=
  prescribedXRFCOutput Q g N (e,nativeOperatorTrialVector P bounds Q g constant N e)

/-- Every partial native virtual output has exactly the fixed-reference
XRFC first variation (the E1 operator response); no trial/output derivative
hypothesis is left beyond the original primitive endpoint C² condition. -/
theorem native_operator_prefix_first_variation (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g : E) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (N : ℕ) (hN : N ≤ n) :
    let tau := nativeOperatorTrialVector P bounds Q g constant N
    HasFDerivAt (nativeOperatorOutput P bounds Q g constant N)
      (fderiv ℝ (fun e => prescribedXRFCOutput Q g N (e,tau 0)) 0) 0 := by
  let tau := nativeOperatorTrialVector P bounds Q g constant N
  let F := nativeOperatorOutput P bounds Q g constant N
  let G := fun e => prescribedXRFCOutput Q g N (e,tau 0)
  have ht := nativeOperatorTrialVector_prefix_contDiffAt P bounds hinit hmax N hN Q hQ hpos
    g constant hg htrial
  have hpre : ∀ i < N, CG.gradient Q g i ≠ 0 := fun i hi => hg i (hi.trans_le hN)
  have hposTau := nativeOperatorTrialVector_zero_pos P bounds Q g constant N
    (fun k hk => (htrial k (hk.trans_le hN)).1)
  have hpsi := prescribedXRFCOutput_contDiffAt Q hQ hpos g N hpre (tau 0) (fun i => (hposTau i).ne')
  have hG : ContDiffAt ℝ 2 G 0 := hpsi.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hb := prescribedXRFC_regular_trial_transfer Q hQ hpos g N hpre (tau 0)
    (fun i => (hposTau i).ne') tau (ht.differentiableAt (by norm_num)) rfl
  have hl : (fun e => F e-G e) =o[𝓝 0] (fun e : Fin (N+1) → E →L[ℝ] E => e) :=
    hb.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < 2))
  have hd : HasFDerivAt (fun e => F e-G e)
      (0 : (Fin (N+1) → E →L[ℝ] E) →L[ℝ] E × E) 0 := by
    apply hasFDerivAt_iff_isLittleO.mpr
    simpa only [F, G, nativeOperatorOutput, tau, sub_self, _root_.zero_apply, sub_zero] using hl
  have hgD := (hG.differentiableAt (by norm_num)).hasFDerivAt
  have h := hd.add hgD
  have heq : ((fun e => F e-G e)+G) = F := by funext e; exact sub_add_cancel _ _
  rw [heq, zero_add] at h
  exact h

/-- The actual native complete/partial point and gradient response is C²
in segment operators, derived from the same original primitive trials. -/
theorem nativeOperatorOutput_contDiffAt (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g : E) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (N : ℕ) (hN : N ≤ n) :
    ContDiffAt ℝ 2 (nativeOperatorOutput P bounds Q g constant N) 0 := by
  have ht := nativeOperatorTrialVector_prefix_contDiffAt P bounds hinit hmax N hN Q hQ hpos
    g constant hg htrial
  have hposTau := nativeOperatorTrialVector_zero_pos P bounds Q g constant N
    (fun k hk => (htrial k (hk.trans_le hN)).1)
  exact (prescribedXRFCOutput_contDiffAt Q hQ hpos g N (fun i hi => hg i (hi.trans_le hN))
    _ (fun i => (hposTau i).ne')).comp 0 (contDiffAt_id.prodMk ht)

end
end krylov.XR
