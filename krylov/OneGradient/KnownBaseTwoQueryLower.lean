import krylov.OneGradient.TwoQueryTransportedGame
import krylov.OneGradient.TwoQueryReferenceGeometry
import krylov.OneGradient.TwoQueryPlane
import krylov.OneGradient.HiddenPlaneFiniteLower
import krylov.OneGradient.HiddenPlaneEndpoints
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), genuine all-M1 finite physical lower bound.
Use: force V2 on the full original known-base two-query source class,
with an explicit uniform finite loss and no competing-policy regularity.
Source: actual arbitrary-query geometry, genuine four symmetric endpoint
matrices, full physical robust-game realization and exact reference scale.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.Information krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- Every actual span-restricted two-query M1 method on the complete
original physical source class obeys the sharp V2 finite lower bound,
up to an explicit common factor tending to one. Its real query or output
may be zero, huge, discontinuous or chosen separately at each radius.
Use: the source asymptotic minimax lower bound has genuine adversaries
and needs no finite-risk premise, CG consistency or limiting query axis.
Article: main_krylov, thm:local(c), original arbitrary-method lower bound.
Proof: rotate a true complete CG frame to the method's actual last query.
Choose the real V2-attaining hidden column and its genuine opposite hidden
endpoint matrices. Their physical transports obey every original budget
and have common real histories within each pair. The actual uniform
guarantee bounds both robust games; the finite four-model theorem and
true reference-length geometry give the result after cancelling the
genuine positive penultimate reference error. -/
theorem knownBaseTwoQueryGuarantee_finite_lower
    (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2)
    (W w omega v : ℝ) (hW : 0< W) (hw : 0< w) (homega : 0< omega)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin 2))) (hm : OneGradientSpanRestricted m)
    (hguarantee : knownBaseTwoQueryGuarantee base g (W*omega) (w*omega) m v) :
    twoDimensionalValue W w*omega^2≤
      (1+(W*omega+w*omega)+(W*omega+w*omega)*(W*omega)/(w*omega)+
        (twoDimensionalValue W w*omega^2)/(w*omega)*(1+W*omega+w*omega))*v := by
  let R := cgOperator (metricRoot base)
  let qv := R (oneGradientStep m (fun _ => cgOperator base) g 1)
  let r := cgOperator (metricRoot base)⁻¹ g+
    R (oneGradientStep m (fun _ => cgOperator base) g 0)+qv
  let q := ‖qv‖
  let sigma := ‖cgCanonicalError base g 1‖
  let eta := W*omega
  let radius := w*omega
  let V := twoDimensionalValue W w
  let L := 1+(eta+radius)+(eta+radius)*eta/radius+(V*omega^2)/radius*(1+eta+radius)
  have heta : 0≤ eta := (mul_pos hW homega).le
  have hradius : 0< radius := mul_pos hw homega
  have hscale := knownBaseCentre_reference_scale base hb g hc
  have hsigma : 0< sigma := by dsimp only [sigma];rw [hscale.2];exact hscale.1
  obtain ⟨he0,hh0,heh0,hfull⟩ := knownBaseCentre_reference_plane base hb g hc
  obtain ⟨e,h,he,hh,heh,hqv⟩ := twoQuery_orthonormal_plane _ _ he0 hh0 heh0 hfull qv
  have hgeom : sigma≤ q+‖r‖ := twoQuery_reference_length_bound base hb g hc m hm
  obtain ⟨a,d,ha,hd,hdisc,hvalue,hgame⟩ := hiddenPlane_finite_reference_lower e h he hh heh r
    W w omega q sigma hW hw homega (norm_nonneg _) hgeom
  let S := planarMatrix e h (hiddenPlaneCentre a d) a d
  let H := planarMatrix e h (hiddenPlaneHalfWidth a d) 0 0
  let K := eta • H
  let Jp := 1+eta • S
  let Jm := 1-eta • S
  let T := inverseFormMap (metricRoot base)⁻¹
  let up := R (m.output (oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator (T Jp))) g 2))
  let um := R (m.output (oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator (T Jm))) g 2))
  let z := (eta*q) • cgOperator S h
  have hSs : S.IsSymm := planarMatrix_isSymm _ _ _ _ _
  have hHs : H.IsSymm := planarMatrix_isSymm _ _ _ _ _
  have hKs : K.IsSymm := hHs.smul eta
  have hJps : Jp.IsSymm := Matrix.isSymm_one.add (hSs.smul eta)
  have hJms : Jm.IsSymm := Matrix.isSymm_one.sub (hSs.smul eta)
  have hHh : cgOperator H h=0 := by
    rw [show cgOperator H=Matrix.toEuclideanCLM (𝕜 := ℝ) H from rfl,planarMatrix_action]
    simp only [heh,mul_zero,zero_mul,add_zero,zero_smul]
  have hhidden : cgOperator K qv=0 := by
    rw [hqv]
    change cgOperator (eta • H) (q • h)=0
    rw [show cgOperator (eta • H)=eta • cgOperator H from map_smul (Matrix.toEuclideanCLM (𝕜 := ℝ)) eta H,
      _root_.smul_apply,map_smul,hHh,smul_zero,smul_zero]
  have hendpoints := hiddenPlane_endpoint_norms e h he hh heh a d hdisc
  have hnorm (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : ‖X‖≤1) : ‖eta • X‖≤ eta := by
    rw [norm_smul,Real.norm_of_nonneg heta]
    exact (mul_le_mul_of_nonneg_left hX heta).trans_eq (mul_one _)
  have hpp : ‖Jp+K-1‖≤ eta := by
    have heq : Jp+K-1=eta • (S+H) := by dsimp only [Jp,K];module
    rw [heq]
    exact hnorm _ hendpoints.1
  have hpm : ‖Jp-K-1‖≤ eta := by
    have heq : Jp-K-1=eta • (S-H) := by dsimp only [Jp,K];module
    rw [heq]
    exact hnorm _ hendpoints.2
  have hmp : ‖Jm+K-1‖≤ eta := by
    have heq : Jm+K-1= -(eta • (S-H)) := by dsimp only [Jm,K];module
    rw [heq,norm_neg]
    exact hnorm _ hendpoints.2
  have hmm : ‖Jm-K-1‖≤ eta := by
    have heq : Jm-K-1= -(eta • (S+H)) := by dsimp only [Jm,K];module
    rw [heq,norm_neg]
    exact hnorm _ hendpoints.1
  have hcolumn : cgOperator S qv=q • cgOperator S h := by rw [hqv,map_smul]
  have hJpv : cgOperator Jp qv=qv+z := by
    simp only [Jp,cgOperator,map_add,map_one,map_smul,_root_.add_apply,_root_.smul_apply,one_apply_eq_self]
    change qv+eta • cgOperator S qv=qv+z
    rw [hcolumn,smul_smul]
  have hJmv : cgOperator Jm qv=qv-z := by
    simp only [Jm,cgOperator,map_sub,map_one,map_smul,_root_.sub_apply,_root_.smul_apply,one_apply_eq_self]
    change qv-eta • cgOperator S qv=qv-z
    rw [hcolumn,smul_smul]
  have hp := twoQuery_transported_game_bound base Jp K hb hJps hKs g eta radius v hradius m hhidden hpp hpm hguarantee
  have hn := twoQuery_transported_game_bound base Jm K hb hJms hKs g eta radius v hradius m hhidden hmp hmm hguarantee
  change twoModelRisk (cgOperator Jp) (cgOperator K) (_+_+cgOperator Jp qv) up radius≤sigma*v at hp
  change twoModelRisk (cgOperator Jm) (cgOperator K) (_+_+cgOperator Jm qv) um radius≤sigma*v at hn
  rw [hJpv] at hp
  rw [hJmv] at hn
  have hplus : twoModelRisk (cgOperator Jp) (cgOperator K) (r+z) up radius≤sigma*v := by
    simpa only [r,add_assoc] using hp
  have hminus : twoModelRisk (cgOperator Jm) (cgOperator K) (r-z) um radius≤sigma*v := by
    simpa only [r,add_sub_assoc] using hn
  have hV : 0≤ V := by dsimp only [V];unfold twoDimensionalValue;split_ifs <;> positivity
  have hL : 0≤ L := by dsimp only [L];positivity
  dsimp only at hgame
  have hlow := hgame up um
  have hbound : (V*omega^2)*sigma≤ L*(sigma*v) :=
    hlow.trans (mul_le_mul_of_nonneg_left (max_le hplus hminus) hL)
  have hnormed : (V*omega^2)*sigma≤(L*v)*sigma := by nlinarith [hbound]
  exact (mul_le_mul_iff_left₀ hsigma).mp hnormed

end
end krylov.OneGradient
