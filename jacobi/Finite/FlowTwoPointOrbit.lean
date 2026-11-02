import jacobi.Finite.FlowWeightLimits

/-!
The complete two-point resolvent orbit.
With two distinct atoms the probability simplex has one free logarithmic
coordinate and the two resolvent velocities differ. Consequently every
positive-weight realization is reached from every other in finite time.
Use: the logarithmic-coordinate discussion identifies when a flow line
passes through the persymmetric point; the two-root case gives an exact
finite-time example reaching every positive realization.
Article: jacobi, Section 5.6, discussion after Corollary 5.7.
Article role: the logarithmic orbit criterion and transitivity of the two-root fibre.
-/
namespace jacobi.Finite
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/-- The actual flow is transitive on every two-point polynomial fibre.
The single log-weight ratio spans the whole fibre, so the orbit reaches
its unique persymmetric member in finite time.
Article: jacobi, Section 5.6, discussion after Corollary 5.7.
-/
theorem resolventFlow_two_point_surjective (S : Nodes 2) (J K : Fiber 2 S.polynomial) :
    ∃ t : ℝ,resolventFlow S J t=K := by
  let w := spectralWeights S J
  let u := spectralWeights S K
  let v := resolventVelocity S
  let d (i : Fin 2) := weightLogs S u i-weightLogs S w i
  let t := (d 0-d 1)/(v 0-v 1)
  let c := d 0-t*v 0
  have hv : v 0-v 1≠0 := (sub_neg.mpr
    (resolventVelocity_strictMono S (by decide : (0:Fin 2)<1))).ne
  have he : (fun i => weightLogs S w i+t*v i)=
      (fun i => weightLogs S u i+(-c)) := by
    funext i
    fin_cases i
    · change weightLogs S w 0+t*v 0=weightLogs S u 0+(-c)
      dsimp only [c,d]
      ring
    · change weightLogs S w 1+t*v 1=weightLogs S u 1+(-c)
      dsimp only [t,c,d]
      field_simp [hv]
      ring
  have hw : resolventWeights S w t=u := by
    unfold resolventWeights
    rw [he,logWeights_shift,logWeights_weightLogs]
  refine ⟨t,?_⟩
  change reconstructFiber S (resolventWeights S w t)=K
  rw [hw]
  exact reconstruct_spectralWeights S K

end
end jacobi.Finite
