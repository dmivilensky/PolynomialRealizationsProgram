import nesterov.Oracle.ResistingOracleRun
import nesterov.Oracle.HardFunction

/-! Every adaptive deterministic policy has a genuine finite-dimensional
smooth strongly convex hard instance, with a hidden terminal coordinate. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped RealInnerProductSpace
variable {J E : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ} (D : ExtensionData J (EuclideanSpace ℝ (Fin (N+1)))) (A : Policy E)

theorem exists_finite_hard_instance
    (hchain : ∀ (j : Fin (N+1)) (y : EuclideanSpace ℝ (Fin (N+1))),
      (∀ m,j.val≤m.val → y m=0) → ∀ m,j.val<m.val → D.support y m=0)
    (xstar : EuclideanSpace ℝ (Fin (N+1)))
    (hstationary : D.field xstar=0) (hnorm : ‖xstar‖≤1)
    (hdim : 2*N+2≤Module.finrank ℝ E) :
    ∃ (f : E→ℝ) (zstar : E),polyak.SmoothStronglyConvex D.q 1 f ∧
      gradient f zstar=0 ∧ ‖zstar‖≤1 ∧
      |xstar (Fin.last N)|≤‖A.result (firstOrderOracle f) N-zstar‖ := by
  obtain ⟨v,hv,ho⟩ := exists_orthogonal_oracle_frame D A hchain hdim
  refine ⟨(D.embed v).potential,frameLift v xstar,(D.embed v).smoothStronglyConvex,?_,?_,?_⟩
  · rw [(D.embed v).gradient_eq,D.embed_field hv,frameCoordinates_lift hv]
    have h := congrArg (frameLift v) hstationary
    simpa only [ExtensionData.field,map_add,map_smul,map_zero,RingHom.id_apply] using h
  · exact (norm_frameLift hv xstar).trans_le hnorm
  · have hlast : inner ℝ (v (Fin.last N)) (frameLift v xstar)=xstar (Fin.last N) :=
      hv.inner_right_fintype xstar (Fin.last N)
    have hp : inner ℝ (v (Fin.last N))
        (A.result (firstOrderOracle (D.embed v).potential) N-frameLift v xstar)= -xstar (Fin.last N) := by
      rw [inner_sub_right,ho,hlast,zero_sub]
    have hb := abs_real_inner_le_norm (v (Fin.last N))
      (A.result (firstOrderOracle (D.embed v).potential) N-frameLift v xstar)
    simpa only [hp,abs_neg,hv.norm_eq_one,one_mul] using hb

end
end nesterov.Oracle

namespace nesterov.Oracle.Geometric
noncomputable section
open scoped RealInnerProductSpace

theorem finite_hard_instance (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (A : Policy (EuclideanSpace ℝ (Fin (2*N+2)))) :
    ∃ (f : EuclideanSpace ℝ (Fin (2*N+2))→ℝ) (zstar : EuclideanSpace ℝ (Fin (2*N+2))),
      polyak.SmoothStronglyConvex (s^2) 1 f ∧ gradient f zstar=0 ∧ ‖zstar‖≤1 ∧
      delta s N≤‖A.result (firstOrderOracle f) N-zstar‖ := by
  have hfield : (data N s hs hs1).field (starPoint N s)=0 := by
    rw [←(data N s hs hs1).gradient_eq]
    exact hardFunction_stationary N hs hs1
  obtain ⟨f,z,hf,hz,hn,hlower⟩ := exists_finite_hard_instance (data N s hs hs1) A
    (fun j y hy=>hardFunction_support_zero_chain N hs hs1 hy)
    (starPoint N s) hfield (starPoint_norm_le hs hs1) (by simp)
  refine ⟨f,z,hf,hz,hn,?_⟩
  simpa only [star_terminal_coordinate,abs_neg,abs_of_pos (delta_pos hs hs1 N)] using hlower

end
end nesterov.Oracle.Geometric
