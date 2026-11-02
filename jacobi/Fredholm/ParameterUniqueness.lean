import jacobi.Fredholm.MassGraph

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Any two physical interior mass roots are joined by the genuine
differentiable mass graph. Strict determinant decrease on this actual
graph proves global uniqueness of the simultaneous mass/determinant root.
Source: the intermediate value theorem, the proved implicit graph and the mean-value theorem.
Use: proves connectedness of the full source mass level between arbitrary candidate pairs.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- Two actual interior mass roots bracket a genuine physical root at every intermediate shape.
Use: proves connectedness of the full source mass level between arbitrary candidate pairs.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: strict mass order reverses the endpoint chi parameters. Shape
monotonicity brackets the desired mass between those two chi values at
every intermediate tau. Actual chi continuity and the intermediate value
theorem produce the root, and strict monotonicity identifies the selector. -/
theorem mass_graph_between {t u c k : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (htu : t<u) (hm : mass t c=mass u k) :
    ∀ v∈Icc t u,massParameter (mass t c) v∈Ioo (0:ℝ) 1 ∧
      mass v (massParameter (mass t c) v)=mass t c := by
  -- Intermediate mass roots are constructed, rather than assumed to belong to an implicit graph.
  have hkc := mass_level_parameter_order ht hu hc hk htu hm
  intro v hv
  have hvp : v∈Ioo (0:ℝ) 1 := ⟨ht.1.trans_le hv.1,hv.2.trans_lt hu.2⟩
  have hcont : ContinuousOn (mass v) (Icc k c) := by
    intro w hw
    exact (mass_parameter_hasDerivAt ⟨hvp.1.le,hvp.2.le⟩
      ⟨hk.1.trans_le hw.1,hw.2.trans_lt hc.2⟩).continuousAt.continuousWithinAt
  have hlo : mass v k≤mass t c := by
    rw [hm]
    exact (mass_shape_strictMono ⟨hk.1,hk.2.le⟩).monotoneOn
      ⟨hvp.1.le,hvp.2.le⟩ ⟨hu.1.le,hu.2.le⟩ hv.2
  have hhi : mass t c≤mass v c :=
    (mass_shape_strictMono ⟨hc.1,hc.2.le⟩).monotoneOn
      ⟨ht.1.le,ht.2.le⟩ ⟨hvp.1.le,hvp.2.le⟩ hv.1
  obtain ⟨w,hw,he⟩ := intermediate_value_Icc hkc.le hcont ⟨hlo,hhi⟩
  have hwp : w∈Ioo (0:ℝ) 1 := ⟨hk.1.trans_le hw.1,hw.2.trans_lt hc.2⟩
  rw [massParameter_eq hvp hwp he]
  exact ⟨hwp,he⟩

/-- The actual determinant restricted to its globally selected mass graph has a genuine strictly negative derivative at every physical root.
Use: gives both continuity and strict mean-value decrease on the connected mass graph.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the implicit function theorem supplies the actual selector
derivative and the zero restricted-mass derivative. The true two-variable
chain rule gives the determinant derivative, whose sign is the already
proved strict Jacobian sign. -/
theorem mass_graph_determinant_calculus {M t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hm : mass t c=M) :
    ∃ D : ℝ,HasDerivAt (fun u => determinant u (massParameter M u)) D t ∧ D<0 := by
  -- Every regularity premise refers to the actual globally selected mass root.
  obtain ⟨b,hb,hM⟩ := massParameter_calculus ht hc hm
  have hp : massParameter M t∈Ioo (0:ℝ) 1 := (massParameter_eq ht hc hm).symm ▸ hc
  have hd := curve_hasDerivAt_of_partials determinant determinantGradient
    (fun u hu v hv => determinant_shape_envelope hu hv)
    (fun u hu v hv => determinant_parameter_envelope hu hv)
    (hasDerivAt_id t) hb ht hp (gradients_continuousAt ht hp).2.2
  refine ⟨deriv (fun u => determinant u (massParameter M u)) t,?_,
    mass_graph_determinant_deriv_neg ht hp hb hM⟩
  simpa only [id_eq] using hd.differentiableAt.hasDerivAt

/-- Increasing the shape strictly decreases the actual determinant between any two physical pairs of the same mass.
Use: proves the global uniqueness assertion for the simultaneous normalized mass and determinant equations.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: construct the actual physical mass graph on the entire interval
joining the two shapes. Its derivative is strictly negative everywhere,
and it is continuous at both endpoints by the genuine implicit derivative.
Apply the strict mean-value theorem and identify its two endpoint roots. -/
theorem determinant_mass_level_order {t u c k : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (htu : t<u) (hm : mass t c=mass u k) : determinant u k<determinant t c := by
  -- Connectedness and differentiability of the original mass level have both been proved.
  let F := fun v => determinant v (massParameter (mass t c) v)
  have hgraph := mass_graph_between ht hu hc hk htu hm
  have hd (v : ℝ) (hv : v∈Icc t u) : ∃ D : ℝ,HasDerivAt F D v ∧ D<0 :=
    mass_graph_determinant_calculus
      ⟨ht.1.trans_le hv.1,hv.2.trans_lt hu.2⟩ (hgraph v hv).1 (hgraph v hv).2
  have hanti : StrictAntiOn F (Icc t u) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc t u)
    · intro v hv
      obtain ⟨D,hD,_⟩ := hd v hv
      exact hD.continuousAt.continuousWithinAt
    · intro v hv
      obtain ⟨D,hD,hneg⟩ := hd v (interior_subset hv)
      rwa [hD.deriv]
  have he := hanti (by exact ⟨le_rfl,htu.le⟩) (by exact ⟨htu.le,le_rfl⟩) htu
  dsimp only [F] at he
  rw [massParameter_eq ht hc rfl,massParameter_eq hu hk hm.symm] at he
  exact he

/-- The simultaneous actual mass and determinant equations have at most one physical interior parameter pair.
Use: closes the unqualified two-parameter uniqueness assertion of the Fredholm theorem.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: unequal shapes give strictly ordered determinants along the
genuine connected mass graph, contradicting equal determinant values.
Equal shapes then force equal chi by strict actual mass monotonicity. -/
theorem interior_root_unique {t u c k M d : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (htM : mass t c=M) (huM : mass u k=M)
    (htD : determinant t c=d) (huD : determinant u k=d) : t=u ∧ c=k := by
  -- The argument applies to arbitrary printed parameter roots, not only to known minimizers.
  have hm := htM.trans huM.symm
  have htu : t=u := by
    rcases lt_trichotomy t u with hlt | heq | hgt
    · have hh := determinant_mass_level_order ht hu hc hk hlt hm
      rw [htD,huD] at hh
      exact (lt_irrefl _ hh).elim
    · exact heq
    · have hh := determinant_mass_level_order hu ht hk hc hgt hm.symm
      rw [htD,huD] at hh
      exact (lt_irrefl _ hh).elim
  refine ⟨htu,?_⟩
  subst u
  exact (mass_parameter_strictMono ⟨ht.1.le,ht.2.le⟩).injOn
    ⟨hc.1.le,hc.2.le⟩ ⟨hk.1.le,hk.2.le⟩ hm

end
end jacobi.Fredholm
