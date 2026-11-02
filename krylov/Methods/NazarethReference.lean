import krylov.Methods.NazarethObserved
import krylov.Methods.NazarethCGStep
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a), genuine Nazareth CG comparison.
Use: derive actual positive CG direction multiples for the literal measured
three-term method, with the original preceding-trial factor retained.
Source: original observed reconstruction identities and the proved true
one/two-direction Lanczos scalar projections; no CG direction field is assumed. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual original Nazareth procedure computes positive multiples of
the true CG directions at every active quadratic query for arbitrary
positive data-dependent trials.
Use: the source classical trajectory comparison concerns the real algorithm
and its real prior-trial scaling, not a supplied scaled-CG sequence.
Article: main_krylov, prop:classical(a), Nazareth77 equation (10).
Proof: true measured direction/image reconstruction recovers exactly the
previous computed directions and their real quadratic images. Induct through
the literal one/two-previous-direction recurrence; its true projection scale
is positive because every actual trial and active CG length is positive. -/
theorem nazareth_direction_reference (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i)) :
    ∀ k<N,∃ scale : ℝ,0<scale ∧
      nazarethDirection trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g k)=scale • CG.direction Q g k := by
  let H := fun k => oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
  have ha (k : ℕ) (hk : k<N) : 0 < CG.length Q g k :=
    (CG.invariant_line_pos Q hpos g k (CG.invariant Q hQ hpos g k
      (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).2.1
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    cases k with
    | zero => exact ⟨1,by norm_num,by simp only [oneGradientRun,nazarethDirection,CG.direction,cgRun,one_smul]⟩
    | succ j =>
      obtain ⟨scale,hscale,hdir⟩ := ih j (by omega) (by omega)
      have htd := nazareth_measured_direction trial (fun _ => Q) g j (ht j (by omega)).ne'
      have hqd := nazareth_measured_image trial (fun _ => Q) g j (ht j (by omega)).ne'
      have htail : historyTail (H (j+1))=H j := oneGradient_historyTail_succ _ _ _ _
      have hrecords : (H (j+1)).records≠[] := by
        have hh := oneGradientRun_length (nazarethMethod trial) (fun _ => Q) g (j+1)
        intro hz
        change (H (j+1)).records.length=j+1 at hh
        rw [hz,List.length_nil] at hh
        omega
      have hform : nazarethDirection trial (H (j+1))=
          trial (H j) • (-Q (scale • CG.direction Q g j)+
            (inner ℝ (Q (scale • CG.direction Q g j)) (Q (scale • CG.direction Q g j))/
              inner ℝ (scale • CG.direction Q g j) (Q (scale • CG.direction Q g j))) • (scale • CG.direction Q g j)+
            (inner ℝ (measuredTrialImage trial (H j)) (Q (scale • CG.direction Q g j))/
              inner ℝ (measuredTrialDirection trial (H j)) (measuredTrialImage trial (H j))) •
                measuredTrialDirection trial (H j)) := by
        unfold nazarethDirection
        split
        · contradiction
        · rw [htail,htd,hqd,hdir]
      cases j with
      | zero =>
        have hfirst := nazareth_first_cg_step Q hQ hpos g (hpre 0 (by omega)) scale hscale.ne'
        have hvalue : nazarethDirection trial (H 1)=
            (trial (H 0)*(scale/CG.length Q g 0)) • CG.direction Q g 1 := by
          rw [hform]
          change trial (H 0) • (-Q (scale • CG.direction Q g 0)+
            (inner ℝ (Q (scale • CG.direction Q g 0)) (Q (scale • CG.direction Q g 0))/
              inner ℝ (scale • CG.direction Q g 0) (Q (scale • CG.direction Q g 0))) • (scale • CG.direction Q g 0)+
            (inner ℝ (measuredTrialImage trial (H 0)) (Q (scale • CG.direction Q g 0))/
              inner ℝ (0 : E) (measuredTrialImage trial (H 0))) • (0 : E))=_
          rw [smul_zero,add_zero,hfirst,smul_smul]
        exact ⟨_,mul_pos (ht 0 (by omega)) (div_pos hscale (ha 0 (by omega))),hvalue⟩
      | succ p =>
        obtain ⟨oldScale,hold,holdDir⟩ := ih p (by omega) (by omega)
        have hod := nazareth_measured_direction trial (fun _ => Q) g p (ht p (by omega)).ne'
        have hoq := nazareth_measured_image trial (fun _ => Q) g p (ht p (by omega)).ne'
        have hstep := nazareth_three_term_cg_step Q hQ hpos g p
          (fun i hi => hpre i (by omega)) scale oldScale hscale.ne' hold.ne'
        have hvalue : nazarethDirection trial (H (p+2))=
            (trial (H (p+1))*(scale/CG.length Q g (p+1))) • CG.direction Q g (p+2) := by
          rw [hform,hod,hoq,holdDir,hstep,smul_smul]
        exact ⟨_,mul_pos (ht (p+1) (by omega)) (div_pos hscale (ha (p+1) (by omega))),hvalue⟩

/-- The genuine arbitrary-trial Nazareth execution stores an independent
basis of the full actual CG flag at every true quadratic prefix.
Use: derive the original predicted-point model domains from literal execution,
without assuming an independent basis or a prescribed reference trajectory.
Article: main_krylov, prop:classical(a,b).
Proof: the proved actual three-term algorithm supplies positive CG direction
multiples. Each positive measured trial adds the genuine next CG direction
outside its old flag; actual recorded-pair induction gives the real basis. -/
theorem nazareth_basis_reference (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
    LinearIndependent ℝ (windowSteps H.pairs) ∧ pairSpan H.pairs=directionFlag Q g k := by
  induction k with
  | zero =>
    constructor
    · change LinearIndependent ℝ (fun i : Fin 0 => windowSteps ([] : List (E × E)) i)
      exact linearIndependent_empty_type
    · change pairSpan ([] : List (E × E))=directionFlag Q g 0
      rw [directionFlag_zero]
      simp only [pairSpan,windowSteps_range,List.not_mem_nil,Set.ofPred_false,Set.image_empty,Submodule.span_empty]
  | succ k ih =>
    let method := nazarethMethod trial
    let H := oneGradientRun method (fun _ => Q) g k
    have hb := ih (by omega)
    obtain ⟨scale,hscale,hdir⟩ := nazareth_direction_reference trial Q hQ hpos g N hpre ht k (by omega)
    have hstep : method.step H=(trial H*scale) • CG.direction Q g k := by
      change trial H • nazarethDirection trial H=_
      rw [hdir,smul_smul]
    have hc : trial H*scale≠0 := (mul_pos (ht k (by omega)) hscale).ne'
    have hd : CG.direction Q g k∉directionFlag Q g k := by
      intro hm
      have hz := directionFlag_conjugate Q hQ hpos g k (fun i hi => hpre i (by omega)) hm
      have hn := (CG.invariant_line_pos Q hpos g k
        (CG.invariant Q hQ hpos g k (fun i hi => hpre i (by omega))) (hpre k (by omega))).1
      exact (hpos _ hn).ne' hz
    have hnew : method.step H∉pairSpan H.pairs := by
      rw [hb.2,hstep]
      intro hm
      have he := Submodule.smul_mem (directionFlag Q g k) (trial H*scale)⁻¹ hm
      rw [smul_smul,inv_mul_cancel₀ hc,one_smul] at he
      exact hd he
    change LinearIndependent ℝ (windowSteps (oneGradientRun method (fun _ => Q) g (k+1)).pairs) ∧ _
    rw [oneGradientRun_pairs_succ]
    constructor
    · rw [windowSteps_cons]
      exact hb.1.finCons hnew
    · rw [pairSpan_cons,hb.2,hstep]
      have he := trial_span_extension (directionFlag Q g k) 0 (CG.direction Q g k)
        (Submodule.zero_mem _) (trial H*scale) hc
      simpa only [zero_add,directionFlag_succ] using he

/-- The actual full observed Nazareth pairs predict exactly the genuine CG
point, gradient and direction on every original positive active reference.
Use: the original classical predicted-point comparison now has its actual
basis and inverse domains derived from the genuine measured recurrence.
Article: main_krylov, prop:classical(b).
Proof: the real Nazareth basis spans the genuine old CG flag; actual quadratic
query balance and actual recorded secants feed the original positive Galerkin
uniqueness theorem, yielding all three real observed-model identities. -/
theorem nazareth_predicted_reference (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
    virtualCorrection H.pairs H.gradient=CG.displacement Q g k-H.displacement ∧
      virtualGradient H.pairs H.gradient=CG.gradient Q g k ∧
        windowDirection H.pairs (virtualGradient H.pairs H.gradient)=CG.direction Q g k := by
  let method := nazarethMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  have hb := nazareth_basis_reference trial Q hQ hpos g N hpre ht k hk
  exact virtual_reference_basis H Q hQ hpos g k (fun i hi => hpre i (hi.trans_le hk))
    (oneGradientRun_quadratic_gradient method Q g k)
    (fun i => oneGradientRun_pairs_quadratic method Q g k (H.pairs.get i) (List.get_mem _ i)) hb.1 hb.2

end
end krylov.Methods
