import krylov.Functions.ReferencePlaneObservedData

/-!
Article: main_krylov, prop:Fcycle(iii) and thm:Fplanar, true source radius.
Use: bound the actual first/last planar displacement by the genuine initial
canonical CG error, retaining the exact constant. Source: true first/last
orthogonal CG projection and the proved exact terminal displacement.
-/
namespace krylov.Functions
noncomputable section
open krylov.Reference krylov.Tensor krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true first/last planar radius is at most the actual full initial
canonical error. No norm comparison is assumed as source data.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem referencePlane_initial_radius (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) :
    ‖canonicalCGStep A g 0‖*Real.sqrt (1+(referencePlaneRatio A hA g)^2)≤‖cgCanonicalError A g 0‖ := by
  obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  change ‖referencePlaneFirst A g‖=1 at he
  change ‖referencePlaneLast A hA g‖=1 at hh
  change inner ℝ (referencePlaneFirst A g) (referencePlaneLast A hA g)=0 at heh
  have hp := hilbertPlaneProject_norm_le (referencePlaneFirst A g) (referencePlaneLast A hA g)
    he hh heh (referencePlaneNode A g (referenceAtomCount A hA g))
  rw [(referencePlane_project_samples A hA g hN).2.2.2,referencePlaneNode_terminal,norm_neg] at hp
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  have hs := plane_norm_sq (planeOfPair (p,r*p))
  change ‖planeOfPair (p,r*p)‖^2=p^2+(r*p)^2 at hs
  have hnon : 0≤1+r^2 := by positivity
  have heq : (p*Real.sqrt (1+r^2))^2=p^2+(r*p)^2 := by
    rw [mul_pow,Real.sq_sqrt hnon]
    ring
  have hn : 0≤p*Real.sqrt (1+r^2) := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have he : p*Real.sqrt (1+r^2)=‖planeOfPair (p,r*p)‖ := by
    nlinarith only [heq,hs,hn,norm_nonneg (planeOfPair (p,r*p))]
  exact he.trans_le hp

end
end krylov.Functions
