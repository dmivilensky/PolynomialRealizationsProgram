import krylov.Functions.NativeRFCTrajectory
import krylov.Functions.MidpointQuadratic

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, genuine ordinary RFC
operator first jets. Use: replace every true search and correction Hessian
average by the slice of the actual third derivative at its true quadratic
reference midpoint. Source: uniform midpoint FTC plus the proved noncircular
native RFC query/reference bootstrap.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A segment between two genuinely enclosed endpoints has the same enclosure.
Article: main_krylov, lem:cycle-transfer, convex query-domain primitive. -/
theorem segment_norm_le_endpoints (a b : E) (R : ℝ) (ha : ‖a‖≤R) (hb : ‖b‖≤R)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : ‖a+t • (b-a)‖≤R := by
  have he : a+t • (b-a)∈closedBall (0:E) R := by
    apply (convex_closedBall (0:E) R).add_smul_mem
      (by simpa only [mem_closedBall,dist_zero_right] using ha) _ ht
    simpa only [add_sub_cancel,mem_closedBall,dist_zero_right] using hb
  simpa only [mem_closedBall,dist_zero_right] using he

/-- The true quadratic search midpoint used by ordinary RFC.
Article: main_krylov, thm:Htransfer. -/
def rfcReferenceSearchMidpoint (Q : E →L[ℝ] E) (u : E) (k : ℕ) : E :=
  fcQuadraticReferencePoint Q u k+(1/2:ℝ) • referenceStep Q (Q u) k

/-- The true ordinary RFC correction midpoint has the next true quadratic
node as its leading term. Article: main_krylov, thm:Htransfer. -/
theorem NativeRFCPrefixBounds.reference_correction_midpoints
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (N : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C N) :
    ∀ k<N,
    let S := rfcFunctionRun T f G fullMemory r (ε • u) k
    let Y := rfcFunctionLinePoint T f fullMemory r (ε • u) S
    let U := rfcFunctionCorrectionStep T f G fullMemory r (ε • u) S
    ‖Y+(1/2:ℝ) • U-ε • fcQuadraticReferencePoint Q u (k+1)‖≤((k:ℝ)+2)*C*ε^2 := by
  intro k hk
  let S := rfcFunctionRun T f G fullMemory r (ε • u) k
  let Y := rfcFunctionLinePoint T f fullMemory r (ε • u) S
  let U := rfcFunctionCorrectionStep T f G fullMemory r (ε • u) S
  let Z := rfcFunctionPoint T f G fullMemory r (ε • u) (k+1)
  have he : Z=Y+U := rfcFunctionPoint_succ_line T f G fullMemory r (ε • u) k
  have hb := midpoint_error_bound Y Z
    (ε • fcQuadraticReferencePoint Q u (k+1)) (ε • fcQuadraticReferencePoint Q u (k+1))
  rw [he,add_sub_cancel_left,sub_self,smul_zero,add_zero] at hb
  have hY := hp.reference_search_points T f G H Q r u ε M D C N k hk
  have hZ := hp.reference_points T f G H Q r u ε M D C N (k+1) (by omega)
  change ‖Y-_‖≤_ at hY
  change ‖Z-_‖≤_ at hZ
  rw [←he] at hb
  have hCe : 0≤C*ε^2 := (norm_nonneg _).trans (hp.2 k hk).2.2.2.1
  exact hb.trans (by push_cast at hZ; nlinarith only [hY,hZ,hCe])

variable [CompleteSpace E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 600000 in
/-- All true ordinary RFC search and correction operators have uniform genuine
third-derivative first jets on every compact nondegenerate reference family.
Article: main_krylov, thm:Htransfer, ordinary RFC compatible tensor inputs.
Only the original Hessian derivative at the minimizer is assumed; all queried
segments, reference replacements and remainders are derived. -/
theorem nativeRFC_reference_operator_jets (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧
      ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u : E, ‖u‖≤R → Q u∈K → ∀ k<N,
      ‖rfcFunctionSearchOperator T f G H fullMemory r (ε • u) k-Q-
        ε • D (rfcReferenceSearchMidpoint Q u k)‖≤η*ε ∧
      ‖rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) k-Q-
        ε • D (fcQuadraticReferencePoint Q u (k+1))‖≤η*ε := by
  obtain ⟨ep,M,Da,C,hep,hM,_,hC,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre R hR
  let rp := r/(‖T.toContinuousLinearMap‖+1)
  have hrp : 0<rp := by dsimp only [rp]; positivity
  have hball : ball (0:E) rp⊆T ⁻¹' closedBall (0:E) r := by
    intro x hx
    rw [mem_preimage,mem_closedBall,dist_zero_right]
    have hx' : ‖x‖≤rp := (by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<rp).le
    have hb := (T.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_left hx' (norm_nonneg _))
    have ht : ‖T.toContinuousLinearMap‖*rp≤r := by
      dsimp only [rp]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖+1)).mpr
      nlinarith only [hr]
    exact hb.trans ht
  have hc : ContinuousOn H (ball 0 rp) :=
    (coordinateDerivative_lipschitz_pullback T H hH).continuousOn.mono hball
  intro η hη
  obtain ⟨ρ,hρ,_,hrem⟩ := averagedHessian_midpoint_expansion H D hrp hc hD
    (η/(2*(M+1))) (by positivity)
  let J := ‖D‖*((N:ℝ)+2)*C
  have hJ : 0≤J := by dsimp only [J]; positivity
  let ε₀ := min ep (min (ρ/(M+1)) (η/(2*(J+1))))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε he u hu hKu k hk
  have heold : ε<ep := he.trans_le (min_le_left _ _)
  have hρscale : M*ε<ρ := by
    have hb := (lt_div_iff₀ (by positivity : 0<M+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [hb,hε]
  have hsmall : J*ε^2≤η/2*ε := by
    have hb := (lt_div_iff₀ (by positivity : 0<2*(J+1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [mul_le_mul_of_nonneg_right hb.le hε.le,sq_nonneg ε]
  have hp := hprefix ε hε heold u hu hKu
  let S := rfcFunctionRun T f G fullMemory r (ε • u) k
  let X := rfcFunctionPoint T f G fullMemory r (ε • u) k
  let Y := rfcFunctionLinePoint T f fullMemory r (ε • u) S
  let U := rfcFunctionCorrectionStep T f G fullMemory r (ε • u) S
  let Z := rfcFunctionPoint T f G fullMemory r (ε • u) (k+1)
  have hx : ‖X‖≤M*ε := (hp.1 k hk.le).1
  have hy : ‖Y‖≤M*ε := (hp.2 k hk).2.2.1
  have hz : ‖Z‖≤M*ε := (hp.1 (k+1) (by omega)).1
  have hZU : Z=Y+U := rfcFunctionPoint_succ_line T f G fullMemory r (ε • u) k
  have hkr : (k:ℝ)+2≤(N:ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hk.le 2
  have hks : (k:ℝ)+1≤(N:ℝ)+2 := by linarith only [hkr]
  have hmidA : ‖X+(1/2:ℝ) • (Y-X)-ε • rfcReferenceSearchMidpoint Q u k‖≤((N:ℝ)+2)*C*ε^2 :=
    (hp.reference_midpoints T f G H Q r u ε M Da C N k hk).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hks hC.le) (sq_nonneg ε))
  have hmidB : ‖Y+(1/2:ℝ) • U-ε • fcQuadraticReferencePoint Q u (k+1)‖≤((N:ℝ)+2)*C*ε^2 :=
    (hp.reference_correction_midpoints T f G H Q r u ε M Da C N k hk).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkr hC.le) (sq_nonneg ε))
  have hbase (a b : E) (ha : ‖a‖≤M*ε) (hb : ‖b‖≤M*ε) :
      ‖averagedDerivative H a (b-a)-Q-D (a+(1/2:ℝ) • (b-a))‖≤η/2*ε := by
    have hh := hrem (M*ε) (by positivity) hρscale a (b-a)
      (fun t ht=>segment_norm_le_endpoints a b (M*ε) ha hb t ht)
    rw [hH₀] at hh
    apply hh.trans
    calc
      _ ≤ η/(2*(M+1))*((M+1)*ε) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hε] : M*ε≤(M+1)*ε) (by positivity)
      _ = η/2*ε := by field_simp
  have hadd (A : E →L[ℝ] E) (a q : E) (hA : ‖A-Q-D a‖≤η/2*ε)
      (ha : ‖a-ε • q‖≤((N:ℝ)+2)*C*ε^2) : ‖A-Q-ε • D q‖≤η*ε := by
    have hs : ‖D a-ε • D q‖≤J*ε^2 := by
      rw [←map_smul,←map_sub]
      exact (D.le_opNorm _).trans ((mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans_eq (by dsimp only [J]; ring))
    have heq : A-Q-ε • D q=(A-Q-D a)+(D a-ε • D q) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add hA (hs.trans hsmall)).trans_eq (by ring))
  constructor
  · exact hadd _ _ _ (hbase X Y hx hy) hmidA
  · have hb := hbase Y Z hy hz
    rw [hZU,add_sub_cancel_left] at hb
    exact hadd _ _ _ hb hmidB

set_option maxHeartbeats 600000 in
/-- A genuine Lipschitz third derivative upgrades all true ordinary RFC
search/correction operator jets to uniform quadratic remainders.
Article: main_krylov, lem:cycle-transfer, the degree-four transfer input.
The derivative and its Lipschitz bound concern the original physical Hessian
on the original metric domain, not a prescribed secant expansion. -/
theorem nativeRFC_reference_operator_jets_quadratic (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L L₃ : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hD : ∀ z : E, ‖T z‖≤r → HasFDerivAt H (D z) z)
    (hDlip : LipschitzOnWith L₃ D (T ⁻¹' closedBall (0:E) r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ Cj : ℝ, 0<ε₀ ∧ 0<Cj ∧
      ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u : E, ‖u‖≤R → Q u∈K → ∀ k<N,
      ‖rfcFunctionSearchOperator T f G H fullMemory r (ε • u) k-Q-
        ε • D 0 (rfcReferenceSearchMidpoint Q u k)‖≤Cj*ε^2 ∧
      ‖rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) k-Q-
        ε • D 0 (fcQuadraticReferencePoint Q u (k+1))‖≤Cj*ε^2 := by
  obtain ⟨ep,M,Da,C,hep,hM,_,hC,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre R hR
  let S := T ⁻¹' closedBall (0:E) r
  have hS : Convex ℝ S := by
    intro a ha b hb u v hu hv huv
    change T (u • a+v • b)∈closedBall (0:E) r
    simpa only [map_add,map_smul] using (convex_closedBall (0:E) r) ha hb hu hv huv
  have hz : (0:E)∈S := by simp [S,hr.le]
  have hd z (hz : z∈S) : HasFDerivAt H (D z) z := hD z
    (by simpa only [S,mem_preimage,mem_closedBall,dist_zero_right] using hz)
  let Cj := (L₃:ℝ)*M^2+‖D 0‖*((N:ℝ)+2)*C+1
  have hCj : 0<Cj := by dsimp only [Cj]; positivity
  let ε₀ := min ep (r/(‖T.toContinuousLinearMap‖*M+1))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Cj,hε₀,hCj,?_⟩
  intro ε hε he u hu hKu k hk
  have hp := hprefix ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  let A := rfcFunctionRun T f G fullMemory r (ε • u) k
  let X := rfcFunctionPoint T f G fullMemory r (ε • u) k
  let Y := rfcFunctionLinePoint T f fullMemory r (ε • u) A
  let U := rfcFunctionCorrectionStep T f G fullMemory r (ε • u) A
  let Z := rfcFunctionPoint T f G fullMemory r (ε • u) (k+1)
  have hx : ‖X‖≤M*ε := (hp.1 k hk.le).1
  have hy : ‖Y‖≤M*ε := (hp.2 k hk).2.2.1
  have hz' : ‖Z‖≤M*ε := (hp.1 (k+1) (by omega)).1
  have hZU : Z=Y+U := rfcFunctionPoint_succ_line T f G fullMemory r (ε • u) k
  have hball (x : E) (hx : ‖x‖≤M*ε) : x∈S := by
    dsimp only [S]
    rw [mem_preimage,mem_closedBall,dist_zero_right]
    have hb := (T.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    change ‖T x‖≤‖T.toContinuousLinearMap‖*(M*ε) at hb
    have he' := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*M+1)).mp
      (he.trans_le (min_le_right _ _))
    nlinarith only [hb,he',hε]
  have hbase (a b : E) (ha : ‖a‖≤M*ε) (hb : ‖b‖≤M*ε) :
      ‖averagedDerivative H a (b-a)-Q-D 0 (a+(1/2:ℝ) • (b-a))‖≤(L₃:ℝ)*M^2*ε^2 := by
    have hh := averagedHessian_midpoint_quadratic H D S hS hz hd hDlip a (b-a) (M*ε)
      (by positivity) (fun t ht=>⟨hball _ (segment_norm_le_endpoints a b _ ha hb t ht),
        segment_norm_le_endpoints a b _ ha hb t ht⟩)
    rw [hH₀] at hh
    exact hh.trans_eq (by ring)
  have hkr : (k:ℝ)+2≤(N:ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hk.le 2
  have hks : (k:ℝ)+1≤(N:ℝ)+2 := by linarith only [hkr]
  have hmidA : ‖X+(1/2:ℝ) • (Y-X)-ε • rfcReferenceSearchMidpoint Q u k‖≤((N:ℝ)+2)*C*ε^2 :=
    (hp.reference_midpoints T f G H Q r u ε M Da C N k hk).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hks hC.le) (sq_nonneg ε))
  have hmidB : ‖Y+(1/2:ℝ) • U-ε • fcQuadraticReferencePoint Q u (k+1)‖≤((N:ℝ)+2)*C*ε^2 :=
    (hp.reference_correction_midpoints T f G H Q r u ε M Da C N k hk).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkr hC.le) (sq_nonneg ε))
  have hadd (A : E →L[ℝ] E) (a q : E)
      (hA : ‖A-Q-D 0 a‖≤(L₃:ℝ)*M^2*ε^2)
      (ha : ‖a-ε • q‖≤((N:ℝ)+2)*C*ε^2) : ‖A-Q-ε • D 0 q‖≤Cj*ε^2 := by
    have hs := ((D 0).le_opNorm (a-ε • q)).trans (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
    rw [map_sub,map_smul] at hs
    have heq : A-Q-ε • D 0 q=(A-Q-D 0 a)+(D 0 a-ε • D 0 q) := by abel
    rw [heq]
    apply (norm_add_le _ _).trans
    dsimp only [Cj]
    nlinarith only [hA,hs,sq_nonneg ε]
  constructor
  · exact hadd _ _ _ (hbase X Y hx hy) hmidA
  · have hb := hbase Y Z hy hz'
    rw [hZU,add_sub_cancel_left] at hb
    exact hadd _ _ _ hb hmidB

end
end krylov.Functions
