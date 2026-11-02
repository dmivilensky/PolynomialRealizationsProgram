import krylov.Methods.HomogeneousVirtual

/-!
Article: main_krylov, lem:U(c,d), true observed virtual-output scaling.
Use: identify the actual virtual correction, extrapolated gradient and real
computed direction on corresponding positively scaled one-gradient prefixes.
Source: exact actual full-window coordinates and proved physical virtual-block covariance.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual full-memory virtual solves scale linearly on genuinely corresponding scaled observed prefixes.
Use: actual XRFC cone homogeneity is derived from primitive old-step and returned-gradient scaling.
Article: main_krylov, lem:U(c,d).
Proof: true old secants scale because they are the actual linear segment
images of the real queried steps. The true finite virtual coordinates scale
by the proved block theorem, and exact observed-window reindexing identifies
all three real computations. -/
theorem oneGradient_virtualBlock_scalar (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (c : ℝ) (hc : c≠0)
    (hs : ∀ i<k, oneGradientStep m A (c • g) i=c • oneGradientStep m A g i)
    (hG : oneGradientGradient m A (c • g) k=c • oneGradientGradient m A g k) :
    let H := oneGradientRun m A g k
    let Hc := oneGradientRun m A (c • g) k
    virtualCorrection (selectedWindow fullMemory Hc) Hc.gradient=
      c • virtualCorrection (selectedWindow fullMemory H) H.gradient ∧
      virtualGradient (selectedWindow fullMemory Hc) Hc.gradient=
        c • virtualGradient (selectedWindow fullMemory H) H.gradient ∧
      windowDirection (selectedWindow fullMemory Hc) (virtualGradient (selectedWindow fullMemory Hc) Hc.gradient)=
        c • windowDirection (selectedWindow fullMemory H) (virtualGradient (selectedWindow fullMemory H) H.gradient) := by
  -- The actual physical operator images scale together with the real old queried displacements.
  let S := fun i : Fin k => oneGradientStep m A g (k-1-i.val)
  let Y := fun i : Fin k => A (k-1-i.val) (S i)
  have hS : (fun i : Fin k => oneGradientStep m A (c • g) (k-1-i.val))=fun i => c • S i :=
    funext fun i => hs _ (by omega)
  have hY : (fun i : Fin k => A (k-1-i.val) (oneGradientStep m A (c • g) (k-1-i.val)))=fun i => c • Y i := by
    funext i
    rw [hs (k-1-i.val) (by omega),map_smul]
  have he := oneGradient_full_virtual_coordinates m A g k
  have hec := oneGradient_full_virtual_coordinates m A (c • g) k
  constructor
  · rw [hec.1,he.1]
    change combine _ (modelCoefficients _ _ (oneGradientGradient m A (c • g) k))=c • _
    rw [hS,hY,hG]
    exact (virtualBlock_scalar S Y (oneGradientGradient m A g k) c hc).1
  constructor
  · rw [hec.2,he.2]
    change oneGradientGradient m A (c • g) k+combine _ (modelCoefficients _ _ (oneGradientGradient m A (c • g) k))=c • _
    rw [hS,hY,hG]
    exact (virtualBlock_scalar S Y (oneGradientGradient m A g k) c hc).2.1
  · rw [oneGradient_full_direction_coordinates,oneGradient_full_direction_coordinates,hec.2,he.2]
    change conjugacyDirection _ _ (oneGradientGradient m A (c • g) k+combine _
      (modelCoefficients _ _ (oneGradientGradient m A (c • g) k)))=c • _
    rw [hS,hY,hG]
    exact (virtualBlock_scalar S Y (oneGradientGradient m A g k) c hc).2.2

end
end krylov.Methods
