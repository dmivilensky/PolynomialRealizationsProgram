import krylov.Envelope.GradientShadow
import krylov.Methods.QuadraticConsistency

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual quadratic information shadow segments.
Use: construct genuine changing line operators whose actual probes and
complete raw-method histories agree exactly with a true single-quadratic
reference, while preserving every real absorbed canonical first increment.
Source: actual moving CG flag compression, genuine nonanticipating
global CG consistency and true finite perturbation differentiation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual moving quadratic shadow segment operators obtained by subtracting the true future absorbed compressions.
Use: The actual moving quadratic shadow segment operators obtained by subtracting the true future absorbed compressions.
Article: main_krylov, apB:lem:mu(c), actual quadratic information shadow segments.
Proof: Retain the genuine static shadow operator and remove exactly the actual future increment tail. -/
def shadowSegments (Q : ℝ → E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) (t : ℝ) (k : ℕ) : E →L[ℝ] E :=
  Q t-t • ∑ l∈Finset.Ico k (N-1), shadowCompression (Q t) (D l) g l

/-- Every true moving quadratic shadow segment starts at the genuine common reference operator.
Use: Every true moving quadratic shadow segment starts at the genuine common reference operator.
Article: main_krylov, apB:lem:mu(c), actual quadratic information shadow segments.
Proof: Its actual future-tail correction is multiplied by the true zero perturbation parameter. -/
theorem shadowSegments_zero (Q : ℝ → E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (g : E) (N k : ℕ) :
    shadowSegments Q D g N 0 k=Q 0 := by simp only [shadowSegments,zero_smul,sub_zero]

/-- The genuine moving shadow segment operators give exactly the actual single-quadratic CG probe answers throughout every true active finite prefix.
Use: The genuine moving shadow segment operators give exactly the actual single-quadratic CG probe answers throughout every true active finite prefix.
Article: main_krylov, apB:lem:mu(c), actual quadratic information shadow segments.
Proof: Every actual future compression kills the genuine current CG direction, so the true finite future-tail action vanishes exactly. -/
theorem shadowSegments_probes (Q : E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) (t : ℝ)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<N, CG.gradient Q g i≠0) :
    ∀ k<N, shadowSegments (fun _ => Q) D g N t k (CG.direction Q g k)=Q (CG.direction Q g k) := by
  -- Each actual future compressed increment kills the true current CG direction before any genuine oracle answer changes.
  intro k hk
  change Q (CG.direction Q g k)-t • (∑ l∈Finset.Ico k (N-1), shadowCompression Q (D l) g l) (CG.direction Q g k)=_
  have hs : (∑ l∈Finset.Ico k (N-1), shadowCompression Q (D l) g l) (CG.direction Q g k)=0 := by
    rw [_root_.sum_apply]
    apply Finset.sum_eq_zero
    intro l hl
    have hmem := Finset.mem_Ico.mp hl
    exact shadowCompression_direction Q (D l) g l k hQ hpos (fun i hi => hpre i (by omega)) hmem.1
  rw [hs,smul_zero,sub_zero]

/-- Every actual globally CG-consistent raw method has exactly the genuine single-quadratic complete history on the true moving shadow segments.
Use: Every actual globally CG-consistent raw method has exactly the genuine single-quadratic complete history on the true moving shadow segments.
Article: main_krylov, apB:lem:mu(c), actual quadratic information shadow segments.
Proof: The actual current CG probes agree exactly; apply the proved genuine nonanticipating full-history shadow theorem, including every true correction query and answer. -/
theorem shadowSegments_methodRun (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : ℝ → E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) (t : ℝ)
    (B : ℕ → E →L[ℝ] E) (hQ : (Q t).toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q t v)) (hpre : ∀ i<N, CG.gradient (Q t) g i≠0) :
    ∀ k≤N, methodRun m (shadowSegments Q D g N t) B g k=
      methodRun m (fun _ => Q t) (fun _ => Q t) g k := by
  apply cgConsistent_shadow m hm (Q t) hQ hpos
  exact shadowSegments_probes (Q t) D g N t hQ hpos hpre
/-- The actual moving shadow segment derivatives are exactly the genuine cumulative absorbed physical increments.
Use: The actual moving shadow segment derivatives are exactly the genuine cumulative absorbed physical increments.
Article: main_krylov, apB:lem:mu(c), actual quadratic information shadow segments.
Proof: True active gradient smoothness gives real moving-compression derivatives; multiplying by the actual perturbation parameter retains only their genuine absorbed reference values. Subtract the true future finite tail from the actual total quadratic derivative. -/
theorem shadowSegments_hasDeriv (Q : ℝ → E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (g : E) (N k : ℕ)
    (hk : k<N) (hQ : HasDerivAt Q (∑ l∈Finset.range (N-1),D l) 0)
    (hG : ∀ i<N, ContDiffAt ℝ 2 (fun t => CG.gradient (Q t) g i) 0)
    (hpre : ∀ i<N, CG.gradient (Q 0) g i≠0)
    (hD : ∀ l<N-1, (D l).toLinearMap.IsSymmetric)
    (hkill : ∀ l<N-1, ∀ i≤l, D l (CG.gradient (Q 0) g i)=0) :
    HasDerivAt (fun t => shadowSegments Q D g N t k) (∑ l∈Finset.range k,D l) 0 := by
  -- Differentiation retains only the actual reference compression because its true multiplier vanishes at zero.
  have hinc (l : ℕ) (hl : l∈Finset.Ico k (N-1)) :
      HasDerivAt (fun t => t • shadowCompression (Q t) (D l) g l) (D l) 0 := by
    have hm := Finset.mem_Ico.mp hl
    have hc := shadowCompression_contDiffAt Q (D l) g l 2 (fun i hi => hG i (by omega))
      (fun i hi => hpre i (by omega))
    have hd := (hasDerivAt_id (0 : ℝ)).smul (hc.differentiableAt (by norm_num)).hasDerivAt
    change HasDerivAt (fun t => t • shadowCompression (Q t) (D l) g l)
      (0 • deriv (fun t => shadowCompression (Q t) (D l) g l) 0+1 • shadowCompression (Q 0) (D l) g l) 0 at hd
    simpa only [one_smul,zero_smul,zero_add,shadowCompression_eq (Q 0) (D l) g l (hD l hm.2) (hkill l hm.2)] using hd
  have hs := HasDerivAt.sum (fun l (hl : l∈Finset.Ico k (N-1)) => hinc l hl)
  have hsplit := Finset.sum_range_add_sum_Ico (f := D) (show k≤N-1 by omega)
  have he : (∑ l∈Finset.range (N-1),D l)-(∑ l∈Finset.Ico k (N-1),D l)=∑ l∈Finset.range k,D l := by
    rw [← hsplit]
    abel
  convert! hQ.sub hs using 1
  · funext t
    simp only [shadowSegments,Finset.smul_sum,Pi.sub_apply,Finset.sum_apply]
  · exact he.symm

end
end krylov.Envelope
