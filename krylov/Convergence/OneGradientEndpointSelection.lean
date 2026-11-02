import krylov.Convergence.OneGradientNormalGeometry
import krylov.OneGradient.FibreExact

/-!
Article: main_krylov, thm:LB, original method-selected endpoint completion.
Use: derive the hidden-coordinate separation from the actual physical
information fibre for every original M1 method. Neither a separated
endpoint nor an assumed output lower bound is a premise.
Source: genuine common query, true completion CG states and reciprocal
last lengths, and the exact two-endpoint harmonic minimax theorem.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Every original span-restricted policy selects at least one real
endpoint completion with the source's sharp relative hidden-coordinate
separation. The last query is genuinely common and may have any sign or
size. Article: main_krylov, thm:LB, fixed-fibre endpoint selection. -/
theorem oneGradient_physical_endpoint_selection
    (method : OneGradientMethod E) (hmeth : OneGradientSpanRestricted method)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1) (blo bhi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<blo)
    (horder : blo≤bhi) :
    let a := lastLanczosVector A hA g hg hc
    let C := lanczosCompletion A hA g hg hc
    let αlo := CG.length (cgOperator (C bhi)) g k
    let αhi := CG.length (cgOperator (C blo)) g k
    let ρ := intervalMinimaxValue αlo αhi
    ∃ b∈({blo,bhi} : Set ℝ), ∃ _hB : (C b).PosDef,
      ρ*|inner ℝ a (oneGradientQuadraticMinimizer (C b) g)|≤
        |inner ℝ a (oneGradientQuadraticMinimizer (C b) g)-
          inner ℝ a (oneGradientLastQuery method (cgOperator (C b)) g k)| := by
  let a := lastLanczosVector A hA g hg hc
  let C := lanczosCompletion A hA g hg hc
  let σ := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let γ := inner ℝ a (CG.gradient (cgOperator A) g k)
  let p := inner ℝ a (oneGradientLastQuery method (cgOperator A) g k)
  have hpos (b : ℝ) (hb : blo≤b) : (C b).PosDef :=
    (lanczos_completion_positive_iff A hA g hg hc b).mpr (hlo.trans_le hb)
  have hfull (b : ℝ) (hb : blo≤b) : referenceAtomCount (C b) (hpos b hb) g=k+1 :=
    completion_full_atoms A hA g hg hc b (hpos b hb)
  have hflag (b : ℝ) (v : E) : v∈CG.krylovSpace (cgOperator (C b)) g k ↔ inner ℝ a v=0 := by
    rw [information_krylov_space (cgOperator A) (cgOperator (C b)) g k
      (lanczos_completion_information A hA g hg hc b) k (by omega)]
    exact krylov_last_lanczos_hyperplane A hA g hg hc v
  have hy (b : ℝ) (hb : blo≤b) :
      inner ℝ a (oneGradientQuadraticMinimizer (C b) g)=(-γ)*CG.length (cgOperator (C b)) g k := by
    rw [oneGradient_normal_minimizer_coordinate (C b) (hpos b hb) g a
      (last_lanczos_unit A hA g hg hc) (hfull b hb) (hflag b)]
    have hh := congrArg CGState.gradient (completion_cg_prefix A hA g hg hc b k le_rfl)
    change CG.gradient (cgOperator (C b)) g k=CG.gradient (cgOperator A) g k at hh
    rw [hh]
    dsimp only [γ]
    ring
  have hα (b : ℝ) : CG.length (cgOperator (C b)) g k=1/(b-σ) := by
    rw [completion_last_cg_length]
    dsimp only [σ]
    congr 1
    ring
  have hαlo : 0<CG.length (cgOperator (C bhi)) g k :=
    cgLength_pos (C bhi) (hpos bhi horder) g k (by rw [hfull bhi horder];omega)
  have hαorder : CG.length (cgOperator (C bhi)) g k≤CG.length (cgOperator (C blo)) g k := by
    rw [hα,hα]
    exact one_div_le_one_div_of_le (sub_pos.mpr hlo) (sub_le_sub_right horder σ)
  obtain ⟨α,hαmem,hsep⟩ := oneGradient_endpoint_coordinate_obstruction
    (CG.length (cgOperator (C bhi)) g k) (CG.length (cgOperator (C blo)) g k) (-γ) p hαlo hαorder
  rcases hαmem with hαmem|hαmem
  · refine ⟨bhi,by simp,hpos bhi horder,?_⟩
    rw [hy bhi horder,oneGradientLastQuery_lanczosCompletion method hmeth A hA g hg hc bhi]
    rw [hαmem] at hsep
    exact hsep.trans_eq (abs_sub_comm _ _)
  · rw [Set.mem_singleton_iff] at hαmem
    refine ⟨blo,by simp,hpos blo le_rfl,?_⟩
    rw [hy blo le_rfl,oneGradientLastQuery_lanczosCompletion method hmeth A hA g hg hc blo]
    rw [hαmem] at hsep
    exact hsep.trans_eq (abs_sub_comm _ _)

end
end krylov.Convergence
