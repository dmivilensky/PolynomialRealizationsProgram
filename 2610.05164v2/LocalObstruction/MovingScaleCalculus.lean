import «2610.05164v2».LocalObstruction.ScalarRootVariation

/-!
Article: 2610.05164v2, Theorem 6.1.
The chain rule for scales that depend on the actual ground parameter.
Use: `«2610.05164v2».LocalObstruction.moving_scale_derivative` feeds
`«2610.05164v2».LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => F (ε,σ (g ε))) (q+c*d*b)
0`.

Use: `«2610.05164v2».LocalObstruction.movingObservationWitness` uses this derivative formula in
the displayed construction of `movingObservationWitness`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem moving_scale_derivative {F : ℝ × ℝ → ℝ} {g σ : ℝ → ℝ} {q c b d : ℝ}
    (hF : DifferentiableAt ℝ F (0,σ (g 0))) (hg : HasDerivAt g b 0)
    (hσ : HasDerivAt σ d (g 0))
    (hq : HasDerivAt (fun t : ℝ => F (t,σ (g 0))) q 0)
    (hc : HasDerivAt (fun t : ℝ => F (0,t)) c (σ (g 0))) :
    HasDerivAt (fun ε : ℝ => F (ε,σ (g ε))) (q+c*d*b) 0 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let D := fderiv ℝ F (0,σ (g 0))
  have hd := hF.hasFDerivAt
  have hdq := hd.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const 0 (σ (g 0))))
  have hdq' : HasDerivAt (fun t : ℝ => F (t,σ (g 0))) (D (1,0)) 0 := by convert! hdq using 1
  have hq' : D (1,0)=q := hdq'.unique hq
  have hdc := hd.comp_hasDerivAt (σ (g 0))
    ((hasDerivAt_const (σ (g 0)) (0:ℝ)).prodMk (hasDerivAt_id (σ (g 0))))
  have hdc' : HasDerivAt (fun t : ℝ => F (0,t)) (D (0,1)) (σ (g 0)) := by convert! hdc using 1
  have hc' : D (0,1)=c := hdc'.unique hc
  have hgraph := hd.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).prodMk (hσ.comp 0 hg))
  have hgraph' : HasDerivAt (fun ε : ℝ => F (ε,σ (g ε))) (D (1,d*b)) 0 := by convert! hgraph using 1
  have hvec : (1,d*b)=(1,0)+(d*b) • ((0,1):ℝ × ℝ) := by ext <;> simp
  have he : D (1,d*b)=q+c*d*b := by rw [hvec,map_add,map_smul,hq',hc',smul_eq_mul];ring
  rw [← he]
  exact hgraph'

end
end «2610.05164v2».LocalObstruction
