import jacobi.Fredholm.Support

/-!
Article: jacobi, Theorem D.7.
Equal printed parameters identify the entire actual Green trajectory and
the actual continuous optimizing density. The argument uses genuine global
uniqueness of the clipped polynomial ODE across the switching boundary.
It does not assume uniqueness of a mass/determinant parameter root.
Source: Picard--Lindelof uniqueness for the proved locally Lipschitz profile field.
Use: the necessity direction of Lemma quad(d) identifies profiles pointwise once their parameter equations have a unique root.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- The printed parameters determine the entire genuine continuous optimizing profile, including both exterior branches.
Use: the necessity direction of Lemma quad(d) identifies profiles pointwise once their parameter equations have a unique root.
Article: jacobi, Theorem D.7.
Proof: the actual inverse parameter formulas identify both autonomous
coefficients and the central Green height; both true central slopes are
zero. Global clipped-ODE uniqueness gives equality of the entire Green
diagonals, and the actual Euler density formulas then give equality of
the original continuous optimizing densities. -/
theorem Optimizer.profile_identified {s M d s' M' d' : ℝ}
    (P : Optimizer s M d) (Q : Optimizer s' M' d') (hs : 0<s) (hs' : 0<s')
    (ht : P.tau hs=Q.tau hs') (hc : P.chi hs=Q.chi hs') :
    P.g hs.le=Q.g hs'.le ∧ (fun x => s*P.density.value x)=(fun x => s'*Q.density.value x) := by
  -- The same actual autonomous initial state determines both full trajectories.
  have hPi := P.inverse_parameters hs
  have hQi := Q.inverse_parameters hs'
  have he : P.edge=Q.edge := by rw [← hPi.2.1,← hQi.2.1,ht,hc]
  have hA : P.A=Q.A := by rw [← P.amplitude_eq hs,← Q.amplitude_eq hs',ht,hc]
  have h0 : P.g hs.le 0=Q.g hs'.le 0 := by rw [← hPi.1,← hQi.1,hc]
  have h1 : deriv (P.g hs.le) 0=deriv (Q.g hs'.le) 0 := by rw [(P.shape hs).2.1,(Q.shape hs').2.1]
  have hPf (x : ℝ) := ((P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).differentiable (by norm_num) x).hasDerivAt
  have hQf (x : ℝ) := ((Q.density.greenDiagonal_contDiff Q.continuous hs'.le Q.pole).differentiable (by norm_num) x).hasDerivAt
  have hQd (x : ℝ) : HasDerivAt (deriv (Q.g hs'.le)) (force P.A P.edge (Q.g hs'.le x)) x := by
    rw [he,hA]
    exact Q.force_hasDerivAt hs' x
  have hgreen := (profile_unique P.A P.edge 0 hPf (P.force_hasDerivAt hs) hQf hQd h0 h1).1
  change P.g hs.le=Q.g hs'.le at hgreen
  refine ⟨hgreen,?_⟩
  funext x
  have hp := P.density_formula hs x
  have hq := Q.density_formula hs' x
  rw [he,hA,hgreen] at hp
  linarith

end
end jacobi.Fredholm
