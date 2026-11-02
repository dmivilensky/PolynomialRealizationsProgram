import krylov.Envelope.ContinuationCompactLimit
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine fixed-tail uniform continuation convergence.
Use: turn actual asymptotic coefficient limits into the true uniform continuation limit on any original compact spectral interval.
Source: the genuine compact-function polynomial state limit, actual point evaluation homomorphism and the real compact sup norm.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Filter
open scoped Topology
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
/-- The actual polynomial evaluated in the genuine continuous-function algebra agrees with the true scalar polynomial at every original point.
Use: The actual polynomial evaluated in the genuine continuous-function algebra agrees with the true scalar polynomial at every original point.
Article: main_krylov, prop:phi(c), genuine fixed-tail uniform continuation convergence.
Proof: Apply the actual point-evaluation algebra homomorphism to genuine polynomial functional calculus. -/
theorem compact_aeval_apply (x : C(K,ℝ)) (p : ℝ[X]) (y : K) :
    (aeval x p) y=p.eval (x y) := by
  have h := Polynomial.aeval_algHom_apply (ContinuousMap.evalAlgHom (S := ℝ) (R := ℝ) y) x p
  exact h.symm

/-- Actual line and recurrence coefficient limits imply genuine uniform convergence of the true fixed-length continuation on every compact real spectral set.
Use: Actual line and recurrence coefficient limits imply genuine uniform convergence of the true fixed-length continuation on every compact real spectral set.
Article: main_krylov, prop:phi(c), genuine fixed-tail uniform continuation convergence.
Proof: Use the actual compact-function norm convergence and its genuine pointwise norm bound, retaining the original scalar polynomial evaluations. -/
theorem continuation_uniform_limit (α β : ℕ → ℝ) (a b : ℝ)
    (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b)) (S : Set ℝ)
    (hS : IsCompact S) (r : ℕ) :
    TendstoUniformlyOn (fun j lam => (phi α β j r).eval lam)
      (fun lam => (phi (fun _ => a) (fun _ => b) 0 r).eval lam) atTop S := by
  -- The original compact spectral set is the genuine domain of the actual sup-norm polynomial state.
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let x : C(S,ℝ) := ⟨fun t => t.val,continuous_subtype_val⟩
  have hx (t : S) : x t=t.val := rfl
  have h := (compact_continuation_limit α β a b hα hβ x r).1
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have hev := (Metric.tendsto_nhds.mp h) eps heps
  filter_upwards [hev] with j hj
  intro lam hlam
  -- Its actual function norm controls every original spectral point by the true evaluation bound.
  have hb := ContinuousMap.norm_coe_le_norm
    (aeval x (phi α β j r)-aeval x (phi (fun _ => a) (fun _ => b) 0 r)) (⟨lam,hlam⟩ : S)
  have he : dist ((phi (fun _ => a) (fun _ => b) 0 r).eval lam) ((phi α β j r).eval lam)≤
      dist (aeval x (phi α β j r)) (aeval x (phi (fun _ => a) (fun _ => b) 0 r)) := by
    rw [dist_comm,dist_eq_norm,dist_eq_norm]
    simpa only [ContinuousMap.sub_apply,compact_aeval_apply,hx] using hb
  exact he.trans_lt hj
end
end krylov.Envelope
