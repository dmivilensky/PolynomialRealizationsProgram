import jacobi.Fredholm.CandidateFeasibility
import jacobi.Fredholm.ProfileIdentification
import jacobi.Fredholm.Exterior
import jacobi.Fredholm.RootIntegral

/-!
Article: jacobi, Theorem D.7.
Every arbitrary physical parameter pair is realized by a genuine
continuous density with its actual inverse Green diagonal and strict
spectral pole margin. Existence uses the proved scalar feasibility and
the direct method; complete parameter uniqueness fixes its exact pair.
All source quadratures, the clipped profile equation and support follow
from the already established actual-optimizer theory.
Source: variational existence and the verified global parameter classification.
Use: discharges arbitrary-candidate existence, spectral identification and attainability in Lemma quad.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- Every physical pair and every positive coupling have a genuine optimizing profile with those exact parameters.
Use: discharges arbitrary-candidate existence, spectral identification and attainability in Lemma quad.
Article: jacobi, Theorem D.7.
Proof: the actual quadratures have positive mass, positive determinant
and strict scalar feasibility. Rescale the mass by the coupling and use
the already proved direct method. The actual optimizer and the prescribed
pair satisfy the same printed conditions; complete parameter uniqueness
therefore identifies their parameters exactly. -/
theorem arbitrary_candidate_exists {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    ∃ P : Optimizer s (mass t c/s) (determinant t c),P.tau hs=t ∧ P.chi hs=c := by
  -- All existence premises are consequences of the printed physical parameter range.
  have hm := mass_pos ⟨ht.1.le,ht.2⟩ ⟨hc.1,hc.2.le⟩
  have hd := determinant_pos ht hc
  have hsm : s*(mass t c/s)=mass t c := by field_simp [hs.ne']
  have hfeas : ENNReal.ofReal (determinant t c)<fredholmTerm s (mass t c/s) := by
    have he : fredholmTerm s (mass t c/s)=fredholmTerm 1 (mass t c) := by
      simp only [fredholmTerm,fredholmLog,hsm,one_mul]
    rw [he]
    exact candidate_strict_feasibility ht hc
  obtain ⟨P⟩ := optimizer_exists hs (div_pos hm hs) hd hfeas
  have hP := P.admissible hs hd.le
  have hpair : admissibleParameters s (mass t c/s) (determinant t c) t c := by
    refine ⟨ht,hc,rfl,?_,?_⟩
    · rw [hsm]
    · intro _
      exact hsm.symm
  exact ⟨P,admissible_parameters_unique hP hpair⟩

/-- A genuine canonical profile for every arbitrary physical pair, chosen from the proved nonempty actual optimizer set.
Use: defines the source family without an assumed profile, Green certificate or feasibility oracle.
Article: jacobi, Theorem D.7.
-/
def candidate (s t c : ℝ) (hs : 0<s) (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    Optimizer s (mass t c/s) (determinant t c) :=
  (arbitrary_candidate_exists hs ht hc).choose

/-- The genuine chosen profile has exactly its prescribed printed shape and determinant parameters.
Use: transports all existing actual-optimizer identities to the arbitrary source family.
Article: jacobi, Theorem D.7.
Proof: these equalities are the proved specification of the nonempty optimizer construction. -/
theorem candidate_parameters {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    (candidate s t c hs ht hc).tau hs=t ∧ (candidate s t c hs ht hc).chi hs=c :=
  (arbitrary_candidate_exists hs ht hc).choose_spec

/-- Every arbitrary candidate has the literal mass, energy, determinant and root-mass quadratures.
Use: closes all four state-integral assertions for arbitrary physical pairs, independently of an edge problem.
Article: jacobi, Theorem D.7.
Proof: the candidate is an actual continuous subcritical optimizing
density with the exact prescribed parameters. Apply the genuine spatial
quadrature theorems and rewrite those parameters; root-mass convergence
is retained explicitly. -/
theorem candidate_state_integrals {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    let P := candidate s t c hs ht hc
    s*P.density.mass=mass t c ∧
    (2*s)^(3/2:ℝ)*P.density.energy=energy t c ∧
    P.density.fredholmReal s=determinant t c ∧
    Integrable (fun x => sqrt (P.density.value x)) ∧
    sqrt (2*s)*(∫ x,sqrt (P.density.value x))=root t c := by
  -- These are integrals of the constructed original density, not normalized stand-ins.
  let P := candidate s t c hs ht hc
  have hpar := candidate_parameters hs ht hc
  have hmass := P.mass_quadrature hs
  have henergy := P.energy_quadrature hs
  have hD := P.determinant_quadrature hs
  have hroot := P.root_quadrature hs
  change P.tau hs=t ∧ P.chi hs=c at hpar
  rw [hpar.1,hpar.2] at hmass henergy hD hroot
  exact ⟨hmass,henergy,hD,hroot⟩

/-- Every arbitrary candidate has the exact printed amplitude, switching level and central Green height.
Use: fixes the original coefficients of its clipped autonomous differential equation.
Article: jacobi, Theorem D.7.
Proof: the actual optimizer's inverse parameter identities and
amplitude normalization hold with its exact prescribed tau and chi. -/
theorem candidate_normalization {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    let P := candidate s t c hs ht hc
    P.A=amplitude t c ∧ P.edge=edge t c ∧ P.g hs.le 0=peak c := by
  -- The source turning value and switching coefficient are the actual inverse Green values.
  let P := candidate s t c hs ht hc
  have hpar := candidate_parameters hs ht hc
  change P.tau hs=t ∧ P.chi hs=c at hpar
  have hi := P.inverse_parameters hs
  have ha := P.amplitude_eq hs
  rw [hpar.1,hpar.2] at hi ha
  exact ⟨ha.symm,hi.2.1.symm,hi.1.symm⟩

/-- Every arbitrary candidate is a continuous strictly subcritical density with a genuine C2 Green diagonal and the printed clipped density formula.
Use: closes actual spectral realization and regularity, without a Green-profile hypothesis.
Article: jacobi, Theorem D.7.
Proof: the constructed candidate is an actual optimizer, so continuity,
the strict pole and classical inverse-Green regularity are already proved.
Rewrite its exact amplitude and switching normalization in its genuine Euler identity. -/
theorem candidate_green_profile {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    let P := candidate s t c hs ht hc
    Continuous P.density.value ∧ s*observe P.density .top<1 ∧
    ContDiff ℝ 2 (P.g hs.le) ∧
    ∀ x : ℝ,2*s*P.density.value x=(amplitude t c)^2*(max (P.g hs.le x-edge t c) 0)^2 := by
  -- The diagonal here is the inverse of the original density's actual operator.
  let P := candidate s t c hs ht hc
  have hn := candidate_normalization hs ht hc
  refine ⟨P.continuous,P.pole,P.density.greenDiagonal_contDiff P.continuous hs.le P.pole,?_⟩
  intro x
  have h := P.density_formula hs x
  change P.A=amplitude t c ∧ P.edge=edge t c ∧ P.g hs.le 0=peak c at hn
  rwa [hn.1,hn.2.1] at h

/-- Every arbitrary candidate has the actual normalized zero first integral, centered turn and strict radial descent.
Use: identifies the inverse-coordinate profile with the source's unique negative phase branch.
Article: jacobi, Theorem D.7.
Proof: the genuine first integral and shape theorem apply to this
actual density. Exact parameter normalization replaces the two
autonomous coefficients and the central Green value by the printed ones. -/
theorem candidate_phase {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    let P := candidate s t c hs ht hc
    P.g hs.le 0=peak c ∧ deriv (P.g hs.le) 0=0 ∧
    (∀ x : ℝ,P.g hs.le (-x)=P.g hs.le x) ∧
    (∀ x : ℝ,0<x → deriv (P.g hs.le) x<0) ∧
    (∀ x : ℝ,(deriv (P.g hs.le) x)^2=phase (amplitude t c) (edge t c) (P.g hs.le x)) := by
  -- The central branch and negative slope are consequences of the original operator, not imposed initial certificates.
  let P := candidate s t c hs ht hc
  have hn := candidate_normalization hs ht hc
  change P.A=amplitude t c ∧ P.edge=edge t c ∧ P.g hs.le 0=peak c at hn
  have hshape := P.shape hs
  refine ⟨hn.2.2,hshape.2.1,hshape.2.2.1,hshape.2.2.2,?_⟩
  intro x
  have h := P.first_integral hs x
  rwa [hn.1,hn.2.1] at h

/-- Every compact arbitrary candidate has the genuine centered finite support and exact matched exponential exterior.
Use: verifies the full exterior assertion for all tau<1, with no assumed switching radius.
Article: jacobi, Theorem D.7.
Proof: the actual candidate has its exact tau<1. Apply the genuine
finite-core and exterior theorem and rewrite the actual switching
coefficient to the printed edge value. -/
theorem candidate_compact_exterior {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    let P := candidate s t c hs ⟨ht.1,ht.2.le⟩ hc
    ∃ a : ℝ,0<a ∧ P.g hs.le a=edge t c ∧
      (∀ x : ℝ,0<P.density.value x ↔ |x|<a) ∧
      (∀ x : ℝ,a≤ |x| → P.g hs.le x-(1/2:ℝ)=(edge t c-(1/2:ℝ))*exp (-2*(|x|-a))) := by
  -- The same actual switching radius controls the support and both exterior half-lines.
  let P := candidate s t c hs ⟨ht.1,ht.2.le⟩ hc
  have hp := candidate_parameters hs ⟨ht.1,ht.2.le⟩ hc
  have hn := candidate_normalization hs ⟨ht.1,ht.2.le⟩ hc
  obtain ⟨a,ha,hb,hpos,hext⟩ := P.compact_exterior hs (by
    change P.tau hs=t ∧ P.chi hs=c at hp
    rw [hp.1]
    exact ht.2)
  change P.A=amplitude t c ∧ P.edge=edge t c ∧ P.g hs.le 0=peak c at hn
  rw [hn.2.1] at hb hext
  exact ⟨a,ha,hb,hpos,hext⟩

/-- Every arbitrary full-support candidate is strictly positive at every finite spatial point.
Use: the complete support dichotomy for the constructed source family.
Article: jacobi, Theorem D.7.
Proof: the actual candidate has precisely tau=1, and its genuine Green
diagonal stays strictly above the switching value one half everywhere. -/
theorem candidate_full_support {s c : ℝ} (hs : 0<s) (hc : c∈Ioo (0:ℝ) 1) (x : ℝ) :
    0<(candidate s 1 c hs (by norm_num) hc).density.value x :=
  (candidate s 1 c hs (by norm_num) hc).full_support hs (candidate_parameters hs (by norm_num) hc).1 x

/-- The actual optimizing density satisfies the unsquared positive-part Euler identity everywhere, including on its zero set.
Use: with candidate_multipliers this is the printed Euler assertion for every arbitrary candidate.
Article: jacobi, Theorem D.7.
Proof: the actual continuous Euler representative equals four ninths
of the squared positive part. Its square root has the positive branch,
giving the printed factor; at a zero density its positive part is zero,
so the unsquared multiplier expression is nonpositive. -/
theorem Optimizer.sqrt_euler {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    (3/2:ℝ)*sqrt (P.density.value x)=max (P.mu*s*(2*P.g hs.le x-1)-P.ell) 0 ∧
      (P.density.value x=0 → P.mu*s*(2*P.g hs.le x-1)-P.ell≤0) := by
  -- The true pointwise Euler representative fixes the square-root sign also at the switching points.
  have hm := congrFun (P.euler hs.le) x
  change P.density.value x=(4/9:ℝ)*(max (P.mu*s*(2*P.g hs.le x-1)-P.ell) 0)^2 at hm
  have hsqrt : (3/2:ℝ)*sqrt (P.density.value x)=max (P.mu*s*(2*P.g hs.le x-1)-P.ell) 0 := by
    rw [hm,sqrt_mul (by norm_num : (0:ℝ)≤4/9),sqrt_sq (le_max_right _ _)]
    norm_num
    ring
  refine ⟨hsqrt,?_⟩
  intro hz
  rw [hz,sqrt_zero,mul_zero] at hsqrt
  exact (le_max_left _ _).trans_eq hsqrt.symm

/-- The arbitrary candidate's actual normal multipliers equal the literal printed amplitude and switching formulas.
Use: verifies the source Euler identity with its specified multipliers, rather than unspecified Lagrange coefficients.
Article: jacobi, Theorem D.7.
Proof: the actual amplitude is (4/3)*mu*s*sqrt(2*s), and the actual
switching level is 1/2+lambda/(2*mu*s). Substitute the proved prescribed
normalization and cancel the positive coupling and multiplier. -/
theorem candidate_multipliers {s t c : ℝ} (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    let P := candidate s t c hs ht hc
    P.mu=3*amplitude t c/(4*s*sqrt (2*s)) ∧
      P.ell=P.mu*s*(2*edge t c-1) := by
  -- The same actual normal multipliers that produced the density are identified explicitly.
  let P := candidate s t c hs ht hc
  have hn := candidate_normalization hs ht hc
  change P.A=amplitude t c ∧ P.edge=edge t c ∧ P.g hs.le 0=peak c at hn
  constructor
  · rw [← hn.1]
    unfold Optimizer.A
    field_simp [hs.ne',(sqrt_pos.mpr (by positivity : 0<2*s)).ne']
    rfl
  · rw [← hn.2.1]
    unfold Optimizer.edge
    field_simp [P.mu_pos.ne',hs.ne']
    ring

/-- Every original centered Fredholm optimizer is exactly the constructed candidate at its printed parameters.
Use: closes the exhaustive profile classification in Lemma quad(d), including the complete actual Green diagonal.
Article: jacobi, Theorem D.7.
Proof: the candidate exists for the original optimizer's actual physical
pair. Both profiles have those same parameters, so the proved global
clipped-ODE uniqueness identifies their genuine Green diagonals and
their scaled densities. Positive coupling cancels in the density identity. -/
theorem Optimizer.eq_candidate {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    let Q := candidate s (P.tau hs) (P.chi hs) hs (P.parameters hs).1 (P.parameters hs).2
    P.g hs.le=Q.g hs.le ∧ P.density.value=Q.density.value := by
  -- The entire profiles are compared; equality is not limited to their four state integrals.
  let Q := candidate s (P.tau hs) (P.chi hs) hs (P.parameters hs).1 (P.parameters hs).2
  have hp := candidate_parameters hs (P.parameters hs).1 (P.parameters hs).2
  change Q.tau hs=P.tau hs ∧ Q.chi hs=P.chi hs at hp
  obtain ⟨hg,hm⟩ := P.profile_identified Q hs hs hp.1.symm hp.2.symm
  refine ⟨hg,?_⟩
  funext x
  have h := congrFun hm x
  nlinarith

end
end jacobi.Fredholm
