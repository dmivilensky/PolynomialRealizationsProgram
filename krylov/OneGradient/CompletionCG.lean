import krylov.OneGradient.CGFibre
import krylov.Reference.Iterates
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(a).
Use: close the whole positive physical information fibre and derive its actual
common CG states, full atom count and variable last measured CG pivot.
Source: genuine Lanczos information geometry, actual CG single-probe execution
and the proved physical positive rank-one criterion.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference
variable {n : ℕ}

/-- The whole original positive information fibre consists exactly of the
constructed physical last-Jacobi-pivot completions on their strict positive half-line.
Use: all possible positive matrices sharing the original information are covered.
Article: main_krylov, s5:fibre(a).
Proof: use the proved whole symmetric operator fibre, then the injective actual
matrix/operator correspondence and independently derived positive pivot domain. -/
theorem physical_information_fibre
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    (C.PosDef ∧ ∀ v∈CG.krylovSpace (cgOperator A) g n,cgOperator C v=cgOperator A v) ↔
      ∃ b : ℝ,lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<b ∧
        C=lanczosCompletion A hA g hg hc b := by
  constructor
  · rintro ⟨hC,hact⟩
    obtain ⟨t,ht⟩ := (krylov_information_rank_one A hA g hg hc (cgOperator C)
      (cgOperator_positive C hC).1).mp hact
    let b := lastJacobiPivot A hA g hg hc+t
    have he : C=lanczosCompletion A hA g hg hc b := by
      apply (Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ)).injective
      change cgOperator C=cgOperator (lanczosCompletion A hA g hg hc b)
      rw [lanczos_completion_operator]
      dsimp only [b]
      rw [add_sub_cancel_left]
      exact ht
    refine ⟨b,?_,he⟩
    exact (lanczos_completion_positive_iff A hA g hg hc b).mp (he ▸ hC)
  · rintro ⟨b,hb,rfl⟩
    exact ⟨(lanczos_completion_positive_iff A hA g hg hc b).mpr hb,
      lanczos_completion_information A hA g hg hc b⟩

/-- Every constructed physical completion has the same actual earlier CG states,
including its final unqueried direction and penultimate gradient.
Use: the source's common last gradient and direction follow from the real executor.
Article: main_krylov, s5:fibre(a).
Proof: its true known action agrees on the actual Krylov flag, and the original
full support derives every nonstagnating query domain before the last pivot. -/
theorem completion_cg_prefix
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) (k : ℕ) (hk : k≤n) :
    cgRun (cgOperator (lanczosCompletion A hA g hg hc b)) g k=cgRun (cgOperator A) g k := by
  have hp := cgOperator_positive A hA
  exact cg_information_prefix _ _ hp.1 hp.2 g
    (fun j hj => cg_nonstagnation A hA g j (by rw [full_gradient_atom_count A hA g hc];omega))
    (lanczos_completion_information A hA g hg hc b) k hk

/-- Every positive last-pivot completion retains exactly the original full atom count.
Use: endpoint completions are genuine full-atom references, including their
actual CG exhaustion and inverse last-step formulas.
Article: main_krylov, s5:fibre(a).
Proof: the actual penultimate gradient is common and nonzero. The genuine
stopping equivalence forces at least the full ambient number of active atoms;
the true spectral support cardinality gives the opposite bound. -/
theorem completion_full_atoms
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (hb : (lanczosCompletion A hA g hg hc b).PosDef) :
    referenceAtomCount (lanczosCompletion A hA g hg hc b) hb g=n+1 := by
  let C := lanczosCompletion A hA g hg hc b
  have hstate := completion_cg_prefix A hA g hg hc b n le_rfl
  have hnon : CG.gradient (cgOperator C) g n≠0 := by
    rw [show CG.gradient (cgOperator C) g n=CG.gradient (cgOperator A) g n from congrArg CGState.gradient hstate]
    exact cg_nonstagnation A hA g n (by rw [full_gradient_atom_count A hA g hc];omega)
  have hlo : n<referenceAtomCount C hb g := by
    exact Nat.lt_of_not_ge (fun h => hnon ((cg_stopping_iff C hb g n).mpr h))
  have hhi : referenceAtomCount C hb g≤n+1 := by
    unfold referenceAtomCount activeSpectralValues
    exact Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _)) |>.trans_eq (by simp)
  change referenceAtomCount C hb g=n+1
  omega

/-- The common actual last direction has the source's exact negative normal
pairing with the genuine last Lanczos vector.
Use: evaluate the rank-one change of its true curvature in original coordinates.
Article: main_krylov, s5:fibre(a).
Proof: insert the derived normal form of the genuine last residual into the
actual CG negative-energy search pairing and cancel its nonzero coefficient. -/
theorem last_cg_normal_direction
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    let z := lastLanczosVector A hA g hg hc
    inner ℝ z (CG.direction (cgOperator A) g n)= -inner ℝ z (CG.gradient (cgOperator A) g n) := by
  let Q := cgOperator A
  let z := lastLanczosVector A hA g hg hc
  let gamma := inner ℝ z (CG.gradient Q g n)
  obtain ⟨hgeom,hgamma⟩ := last_cg_gradient_normal A hA g hg hc
  have hp := cgOperator_positive A hA
  have hs := (CG.invariant Q hp.1 hp.2 g n
    (fun j hj => cg_nonstagnation A hA g j (by rw [full_gradient_atom_count A hA g hc];omega))).search_pair
  rw [hgeom,real_inner_smul_right,real_inner_comm z (CG.direction Q g n),norm_smul,
    last_lanczos_unit A hA g hg hc,Real.norm_eq_abs,mul_one,sq_abs] at hs
  change gamma≠0 at hgamma
  change inner ℝ z (CG.direction Q g n)= -gamma
  apply mul_left_cancel₀ hgamma
  nlinarith

/-- Every genuinely queried earlier CG line length is common to the physical fibre.
Use: the actual penultimate iterate is independent of the unmeasured last curvature.
Article: main_krylov, s5:fibre(a).
Proof: the actual state and its true old-flag direction action are common. -/
theorem completion_cg_earlier_length
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) (k : ℕ) (hk : k<n) :
    CG.length (cgOperator (lanczosCompletion A hA g hg hc b)) g k=CG.length (cgOperator A) g k := by
  have hstate := completion_cg_prefix A hA g hg hc b k hk.le
  change lineLength (cgRun _ g k).gradient (cgRun _ g k).direction
    (cgOperator (lanczosCompletion A hA g hg hc b) (cgRun _ g k).direction)=_
  rw [hstate]
  have hp := cgOperator_positive A hA
  have hflag : CG.direction (cgOperator A) g k∈CG.krylovSpace (cgOperator A) g n := by
    apply krylov.Envelope.krylovSpace_mono _ _ (show k+1≤n by omega)
    apply krylov.Envelope.cgDirection_mem_krylov
    intro i hi
    exact ((CG.invariant _ hp.1 hp.2 g (k+1) (fun j hj => cg_nonstagnation A hA g j
      (by rw [full_gradient_atom_count A hA g hc];omega))).lines_pos i hi).ne'
  rw [lanczos_completion_information A hA g hg hc b _ hflag]

/-- The actual penultimate physical CG iterate is common across all last-pivot completions.
Use: the information minimax reduction uses the true common CG reference point.
Article: main_krylov, s5:fibre(a).
Proof: each actual earlier searched displacement has the common measured
line and common genuine reference direction. -/
theorem completion_cg_displacement
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    CG.displacement (cgOperator (lanczosCompletion A hA g hg hc b)) g n=CG.displacement (cgOperator A) g n := by
  unfold CG.displacement
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  rw [completion_cg_earlier_length A hA g hg hc b k hkn]
  exact congrArg (fun d => CG.length (cgOperator A) g k • d)
    (congrArg CGState.direction (completion_cg_prefix A hA g hg hc b k hkn.le))

/-- The actual common last direction has precisely the affine physical
curvature dictated by the single free inverse pivot.
Use: the last CG step is derived from real observed pairings, not assigned as
an abstract function of the completion parameter.
Article: main_krylov, s5:fibre(a).
Proof: normalize the genuine last residual by the actual unit normal, use
the executed CG line formula for its original curvature and insert the true
rank-one completion's measured curvature change. -/
theorem completion_last_curvature
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    let z := lastLanczosVector A hA g hg hc
    let d := CG.direction (cgOperator A) g n
    let gamma := inner ℝ z (CG.gradient (cgOperator A) g n)
    inner ℝ d (cgOperator (lanczosCompletion A hA g hg hc b) d)=
      gamma^2*(b-lastJacobiPivot A hA g hg hc+(lastInversePivot A hA g hg hc)⁻¹) := by
  let Q := cgOperator A
  let z := lastLanczosVector A hA g hg hc
  let d := CG.direction Q g n
  let r := CG.gradient Q g n
  let a := CG.length Q g n
  let gamma := inner ℝ z r
  obtain ⟨hgeom,hgamma⟩ := last_cg_gradient_normal A hA g hg hc
  have hp := cgOperator_positive A hA
  have hinv := CG.invariant Q hp.1 hp.2 g n (fun j hj => cg_nonstagnation A hA g j
    (by rw [full_gradient_atom_count A hA g hc];omega))
  obtain ⟨hd,ha,hlen⟩ := CG.invariant_line_pos Q hp.2 g n hinv (cg_nonstagnation A hA g n
    (by rw [full_gradient_atom_count A hA g hc];omega))
  change r=gamma • z at hgeom
  have hnorm : ‖r‖^2=gamma^2 := by
    rw [hgeom,norm_smul,last_lanczos_unit A hA g hg hc,Real.norm_eq_abs,mul_one,sq_abs]
  have hcurv : inner ℝ d (Q d)=gamma^2/a := by
    apply (eq_div_iff ha.ne').mpr
    have hcpos := hp.2 d hd
    have hh := (eq_div_iff hcpos.ne').mp hlen
    rw [hnorm] at hh
    simpa only [mul_comm] using hh
  have hzd : inner ℝ z d= -gamma := last_cg_normal_direction A hA g hg hc
  dsimp only
  rw [lanczos_completion_operator]
  change inner ℝ d ((Q+(b-lastJacobiPivot A hA g hg hc) • InnerProductSpace.rankOne ℝ z z) d)=_
  simp only [_root_.add_apply,_root_.smul_apply,InnerProductSpace.rankOne_apply,
    inner_add_right,real_inner_smul_right]
  rw [real_inner_comm z d,hzd,hcurv,last_inverse_pivot_cg_length A hA g hg hc]
  change gamma^2/a+(b-lastJacobiPivot A hA g hg hc)*((-gamma)*(-gamma))=
    gamma^2*(b-lastJacobiPivot A hA g hg hc+a⁻¹)
  ring

/-- The actual last CG length on the entire physical fibre is the reciprocal
of its only unresolved affine Jacobi pivot.
Use: connect the source's scalar information interval to the genuine CG executor.
Article: main_krylov, s5:fibre(a), alpha(b)=1/(b-sigma).
Proof: the common real state gives the original nonzero residual numerator;
the proved actual affine curvature gives the denominator, and the common
nonzero squared normal coefficient cancels exactly. -/
theorem completion_last_cg_length
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    CG.length (cgOperator (lanczosCompletion A hA g hg hc b)) g n=
      1/(b-lastJacobiPivot A hA g hg hc+(lastInversePivot A hA g hg hc)⁻¹) := by
  let z := lastLanczosVector A hA g hg hc
  let gamma := inner ℝ z (CG.gradient (cgOperator A) g n)
  obtain ⟨hgeom,hgamma⟩ := last_cg_gradient_normal A hA g hg hc
  have hp := cgOperator_positive A hA
  have hsearch := (CG.invariant _ hp.1 hp.2 g n (fun j hj => cg_nonstagnation A hA g j
    (by rw [full_gradient_atom_count A hA g hc];omega))).search_pair
  change lineLength (cgRun _ g n).gradient (cgRun _ g n).direction
    (cgOperator (lanczosCompletion A hA g hg hc b) (cgRun _ g n).direction)=_
  rw [completion_cg_prefix A hA g hg hc b n le_rfl]
  unfold lineLength
  rw [hsearch,neg_neg,hgeom,norm_smul,last_lanczos_unit A hA g hg hc,
    Real.norm_eq_abs,mul_one,sq_abs,completion_last_curvature]
  rw [div_mul_eq_div_div,div_self (pow_ne_zero 2 hgamma)]

end
end krylov.OneGradient
