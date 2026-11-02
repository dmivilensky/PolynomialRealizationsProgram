import krylov.Correction.PrefixResidual
import krylov.Stability.RFCPairOrders

/-!
Article: main_krylov, apD:prefix and thm:C, actual RFC search residual identities.
Use: derive the incoming last-correction residual from the real observed
conjugacy solve and the actual recorded secant discrepancy.
Source: the proved actual RFC reference domains, fixed chronological window
coordinates and exact recorded-pair/operator-mismatch identity.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual full-memory RFC direction annihilates every actual old secant near its positive quadratic reference.
Use: derive the old-image conjugacy premise from the genuine executed coefficient solve.
Article: main_krylov, apD:prefix, y_iᵀd_k=0.
Proof: the actual chronological conjugacy matrix is analytic and has the
proved nonsingular CG reference value. Its true inverse-domain neighborhood
therefore justifies the real coefficient-solve equations for every old image. -/
theorem full_old_conjugacy_eventually (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    ∀ᶠ z in 𝓝 (0 : X), ∀ i<k,
      inner ℝ (probedSecant (rfcMethod fullMemory count) (A z) (B z) (g z) i)
        ((rfcMethod fullMemory count).direction
          (methodRun (rfcMethod fullMemory count) (A z) (B z) (g z) k))=0 := by
  -- Derive a genuine common local inverse domain for the real old-image solve.
  let m := rfcMethod fullMemory count (E := E)
  let H := fun z => methodRun m (A z) (B z) (g z) k
  let S := fun z (j : Fin k) => probedStep m (A z) (B z) (g z) (k-1-j.val)
  let Y := fun z (j : Fin k) => probedSecant m (A z) (B z) (g z) (k-1-j.val)
  let C := fun z => crossGram (Y z) (S z)
  have hm : ∀ j, CG.gradient Q (g 0) j≠0 → 0<j → 0<fullMemory j := fun _ _ hj => hj
  have ht := quadraticRFC_prefix_analytic fullMemory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun i hi => hpre i (by omega))
  have hC : AnalyticAt ℝ C 0 := analytic_spectral_matrix C 0 fun i j =>
    analytic_inner (ht.2 (k-1-i.val) (by omega)).2.2 (ht.2 (k-1-j.val) (by omega)).2.1
  have hC₀ : (C 0).det≠0 := by
    have hr := (rfc_reference_coordinate_domains fullMemory count Q hQ hpos (g 0) hm k hpre).1
    rw [show min (fullMemory k) k=k from min_self k] at hr
    dsimp only [C,S,Y]
    rw [hA0,hB0]
    exact hr
  have hu : ∀ᶠ z in 𝓝 (0 : X), IsUnit (C z).det :=
    ((continuous_id.matrix_det.continuousAt.comp hC.continuousAt).eventually_ne hC₀).mono
      fun _ hz => isUnit_iff_ne_zero.mpr hz
  filter_upwards [hu] with z hz i hi
  have hd : m.direction (H z)=conjugacyDirection (S z) (Y z) (H z).gradient := by
    change windowDirection (selectedWindow fullMemory (H z)) (H z).gradient=_
    rw [selectedWindow_methodRun,windowDirection_executed_take]
    rw [show min (fullMemory k) k=k from min_self k]
  have hc := congrFun (conjugacyDirection_conjugate (S z) (Y z) (H z).gradient hz)
    ⟨k-1-i,by omega⟩
  rw [← hd] at hc
  simpa only [Y,coordinates,Fin.val_mk,Pi.zero_apply,show k-1-(k-1-i)=i by omega,m,H] using hc

/-- Exact old-step search residual in the presence of an actual measured-pair defect.
Use: isolate old projected residual, fresh operator drift and pair discrepancy before taking orders.
Article: main_krylov, apD:prefix, old-coordinate identity before the final model solve.
Proof: move the old symmetric operator across the inner product and eliminate
its action by the genuine observed-image conjugacy equation. -/
theorem search_pair_identity (A C : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (s y xi line g : E) (hy : y=A s+xi) (hconj : inner ℝ y line=0) :
    inner ℝ s (g+C line)=inner ℝ s g+inner ℝ s ((C-A) line)-inner ℝ xi line := by
  have hsym := hA s line
  change inner ℝ (A s) line=inner ℝ s (A line) at hsym
  rw [hy,inner_add_left,hsym] at hconj
  simp only [inner_add_right,_root_.sub_apply,inner_sub_right]
  linarith

/-- Actual full-memory RFC has the exact old-coordinate incoming-residual identity on a derived neighborhood.
Use: the fresh-defect expansion starts from actual search and correction observations.
Article: main_krylov, thm:C and apD:prefix, exact pre-correction residual.
Proof: genuine local observed conjugacy annihilates the actual line step;
the real secant-defect identity supplies the actual discrepancy. Apply the
elementary symmetric search identity to each real old recorded step. -/
theorem full_search_pair_identity_eventually (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory count (E := E)
    let H := fun z => methodRun m (A z) (B z) (g z) k
    let d := fun z => m.direction (H z)
    let line := fun z => lineLength (H z).gradient (d z) (A z k (d z)) • d z
    ∀ᶠ z in 𝓝 (0 : X), ∀ i<k,
      inner ℝ (probedStep m (A z) (B z) (g z) i)
        (searchedGradient (H z).gradient (d z) (A z k (d z))) =
      inner ℝ (probedStep m (A z) (B z) (g z) i) (H z).gradient+
        inner ℝ (probedStep m (A z) (B z) (g z) i) ((A z k-A z i) (line z))-
        inner ℝ (probedSecant m (A z) (B z) (g z) i-
          A z i (probedStep m (A z) (B z) (g z) i)) (line z) := by
  -- Every equality is on the real execution neighborhood of the genuine conjugacy solve.
  let m := rfcMethod fullMemory count (E := E)
  let H := fun z => methodRun m (A z) (B z) (g z) k
  let d := fun z => m.direction (H z)
  let line := fun z => lineLength (H z).gradient (d z) (A z k (d z)) • d z
  filter_upwards [full_old_conjugacy_eventually count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre]
    with z hz i hi
  have hc : inner ℝ (probedSecant m (A z) (B z) (g z) i) (line z)=0 := by
    rw [real_inner_smul_right,hz i hi,mul_zero]
  have he := search_pair_identity (A z i) (A z k) (hAsym z i)
    (probedStep m (A z) (B z) (g z) i) (probedSecant m (A z) (B z) (g z) i)
    (probedSecant m (A z) (B z) (g z) i-A z i (probedStep m (A z) (B z) (g z) i))
    (line z) (H z).gradient (by abel) hc
  simpa only [searchedGradient,map_smul,line] using he

end
end krylov.Correction
