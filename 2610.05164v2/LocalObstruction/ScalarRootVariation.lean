import «2610.05164v2».LocalObstruction.ScalarImplicit

/-!
Article: 2610.05164v2, Theorem 6.1.
Differentiating a scalar implicit equation recovers the derivative of its actual root from the two
actual partial derivatives.
Use: `«2610.05164v2».LocalObstruction.scalar_root_variation` feeds
`«2610.05164v2».LocalObstruction.groundCoupling_density_derivative` (ground Coupling density
derivative).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Filter
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
Exact identity `q+c*b=0`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_density_derivative` uses this identity to
establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => groundCoupling
(m+ε • v)) (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/ (∫ x,m
x*(H1.rep G.u x)^2)) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem scalar_root_variation {F : ℝ × ℝ → ℝ} {g : ℝ → ℝ} {q c b : ℝ}
    (hF : DifferentiableAt ℝ F (0,g 0)) (hg : HasDerivAt g b 0)
    (hz : ∀ᶠ x in 𝓝 0,F (x,g x)=F (0,g 0))
    (hq : HasDerivAt (fun t : ℝ => F (t,g 0)) q 0)
    (hc : HasDerivAt (fun t : ℝ => F (0,t)) c (g 0)) : q+c*b=0 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let D := fderiv ℝ F (0,g 0)
  have hd := hF.hasFDerivAt
  have hdq := hd.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const 0 (g 0)))
  have hdq' : HasDerivAt (fun t : ℝ => F (t,g 0)) (D (1,0)) 0 := by convert! hdq using 1
  have hq' : D (1,0)=q := hdq'.unique hq
  have hdc := hd.comp_hasDerivAt (g 0) ((hasDerivAt_const (g 0) (0:ℝ)).prodMk (hasDerivAt_id (g 0)))
  have hdc' : HasDerivAt (fun t : ℝ => F (0,t)) (D (0,1)) (g 0) := by convert! hdc using 1
  have hc' : D (0,1)=c := hdc'.unique hc
  have hgraph := hd.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).prodMk hg)
  have hgraph' : HasDerivAt (fun t : ℝ => F (t,g t)) (D (1,b)) 0 := by convert! hgraph using 1
  have hconstant : HasDerivAt (fun t : ℝ => F (t,g t)) 0 0 :=
    (hasDerivAt_const (0:ℝ) (F (0,g 0))).congr_of_eventuallyEq hz
  have hb : D (1,b)=0 := hgraph'.unique hconstant
  have hvec : (1,b)=(1,0)+b • ((0,1):ℝ × ℝ) := by ext <;> simp
  rw [hvec,map_add,map_smul,hq',hc',smul_eq_mul] at hb
  linarith

end
end «2610.05164v2».LocalObstruction
