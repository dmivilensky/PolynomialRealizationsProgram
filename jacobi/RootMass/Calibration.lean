import jacobi.RootMass.StateIntegrals

/-!
Article: jacobi, Theorem 3.2.
The actual attained inner problem is evaluated at the unique parameter of
the printed nonsingular quadrature. Weak duality then applies to every
original exact-mass, root-bounded competitor, including a negative mass
multiplier. No Euler equation, optimizer, or quadrature certificate is a premise.
Source: the proved actual inner minimizer and the original variational definitions.
Use: the final bound has a defined parameter for every positive b and spectral threshold.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- The actual unique quadrature parameter of the root-mass calibration.
Use: the final bound has a defined parameter for every positive b and spectral threshold.
Article: jacobi, Theorem D.8.
-/
def parameter (a b T : ℝ) (ha : -(17/5:ℝ)≤a) (hb : 0<b) (hT : 0<T) : ℝ :=
  Classical.choose (constraint_root ha (div_pos hT (pow_pos hb 4)))

/-- The defined calibration parameter is positive and satisfies the genuine printed constraint.
Use: discharges the root premise of the explicit inner value and final lower bound.
Article: jacobi, Theorem D.8.
Proof: select the already constructed actual unique positive root. -/
theorem parameter_spec {a b T : ℝ} (ha : -(17/5:ℝ)≤a) (hb : 0<b) (hT : 0<T) :
    0<parameter a b T ha hb hT ∧
      Ghat a (sharp_parameter ha) (parameter a b T ha hb hT)=T/b^4 := by
  exact ⟨(Classical.choose_spec (constraint_root ha (div_pos hT (pow_pos hb 4)))).1,
    (Classical.choose_spec (constraint_root ha (div_pos hT (pow_pos hb 4)))).2.1⟩

/-- The actual inner infimum has its exact printed attained value at every genuine defining root.
Use: weak duality evaluates the minimum of all densities, not just the objective of an explicit candidate.
Article: jacobi, Theorem 3.2.
Proof: construct an actual compact optimizer. Its actual spectral quadrature
and the proved strict monotonicity identify its parameter with y. Substitute
the three proved actual state integrals into its attained objective. -/
theorem inner_exact {a b T y : ℝ} (ha : -(17/5:ℝ)≤a) (hb : 0<b) (hT : 0<T)
    (hy : 0<y) (hroot : Ghat a (sharp_parameter ha) y=T/b^4) :
    inner a b T=ENNReal.ofReal (b^3*hat 3 a (sharp_parameter ha) y+
      (a*b/2)*(b^2*hat 2 a (sharp_parameter ha) y)+b^3*hat 1 a (sharp_parameter ha) y) := by
  -- Unconditional actual attainment precedes every explicit evaluation.
  obtain ⟨P⟩ := profile_exists (sharp_parameter ha) hb hT
  have hPy : Ghat a (sharp_parameter ha) P.y=T/b^4 := by
    apply (eq_div_iff (pow_ne_zero 4 hb.ne')).mpr
    nlinarith [P.constraint (sharp_parameter ha) hb hT]
  have he : P.y=y := (Ghat_strictMono ha).injOn (P.y_pos hb).le hy.le (hPy.trans hroot.symm)
  rw [← P.optimal,RootDensity.cost,P.density.objective_terms,
    P.energy (sharp_parameter ha) hb,P.mass (sharp_parameter ha) hb,P.rootIntegral (sharp_parameter ha) hb,he]
  congr 1
  ring

/-- The literal root-mass Lagrangian lower bound, in the parameter a=eta/2.
Use: specializes to the article's ell_H at the constructed unique parameter.
Article: jacobi, Theorem D.8.
-/
def ellH (a b M : ℝ) (ha : -(17/5:ℝ)≤a) (y : ℝ) : ℝ :=
  b^3*hat 3 a (sharp_parameter ha) y+
    (a*b/2)*(b^2*hat 2 a (sharp_parameter ha) y-M)+
    b^2*(b*hat 1 a (sharp_parameter ha) y-1)

/-- The exact root-mass Lagrangian estimate holds on the full original variational domain.
Use: the article's edge-spectrum theorem follows by substituting its actual mass and second-moment threshold.
Article: jacobi, Theorem D.8.
Proof: every admissible competitor has a genuine finite root integral by
its extended root-mass bound. The computed actual inner infimum bounds its
full penalized objective. Exact mass cancels the signed mass penalty, and
root mass at most one bounds the nonnegative root penalty by b². -/
theorem root_calibration {a b M : ℝ} (ha : -(17/5:ℝ)≤a) (hb : 0<b)
    (T : Observation → ℝ) (hT : 0<T .second) :
    ENNReal.ofReal (ellH a b M ha (parameter a b (T .second) ha hb hT))≤
      rootInfimum {Observation.second} M T := by
  -- Weak duality is applied directly to the literal full admissible set.
  let y := parameter a b (T .second) ha hb hT
  have hy := parameter_spec ha hb hT
  have hinner := inner_exact ha hb hT hy.1 hy.2
  apply le_sInf
  rintro v ⟨m,⟨hmM,hmR,hmT⟩,rfl⟩
  have hR : m.rootMass≤ENNReal.ofReal (1:ℝ) := by simpa only [ENNReal.ofReal_one] using hmR
  obtain ⟨hi,hr⟩ := m.root_integrable_of_bound zero_le_one hR
  let q : RootDensity := ⟨m,hi⟩
  have hlo : inner a b (T .second)≤q.cost a b := sInf_le ⟨q,hmT .second (by simp),rfl⟩
  rw [hinner,RootDensity.cost] at hlo
  have hreal := (ENNReal.ofReal_le_ofReal_iff (q.objective_nonneg (sharp_parameter ha) hb.le)).mp hlo
  rw [q.objective_terms] at hreal
  have hmass : q.mass=M := hmM
  have hroot : q.rootIntegral≤1 := hr
  rw [hmass] at hreal
  apply ENNReal.ofReal_le_ofReal
  change ellH a b M ha y≤m.energy
  unfold ellH
  nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hroot)]

/-- The literal edge-spectrum root-mass calibration throughout the complete printed eta range.
Use: applies the completed analytic calibration directly to every edge spectrum of jacobi.
Article: jacobi, Theorem D.8.
Proof: positivity of the actual edge spectrum gives its positive second
moment. The proved quadrature theorem constructs the unique positive root,
and unconditional weak duality gives exactly the printed ell_H bound. -/
theorem edge_calibration (Λ : EdgeSpectrum) {eta b : ℝ} (heta : -(34/5:ℝ)≤eta) (hb : 0<b) :
    ∃ ha : -(17/5:ℝ)≤eta/2,∃ y : ℝ,0<y ∧
      Ghat (eta/2) (sharp_parameter ha) y=Λ.second/b^4 ∧
      (∀ z : ℝ,0<z → Ghat (eta/2) (sharp_parameter ha) z=Λ.second/b^4 → z=y) ∧
      ENNReal.ofReal (ellH (eta/2) b Λ.mass ha y)≤
        rootInfimum {Observation.second} Λ.mass (threshold Λ) := by
  -- The actual spectral data discharge all positivity hypotheses internally.
  have ha : -(17/5:ℝ)≤eta/2 := by linarith
  have hsum := jacobi.Continuum.summable_powers Λ.summable (fun n => (Λ.positive n).le) (by decide : 0<2)
  have hT : 0<Λ.second := (sq_pos_of_pos (Λ.positive 0)).trans_le
    (hsum.le_tsum 0 (fun n _ => sq_nonneg (Λ.value n)))
  let y := parameter (eta/2) b Λ.second ha hb hT
  have hy := parameter_spec ha hb hT
  have huniq (z : ℝ) (hz : 0<z) (he : Ghat (eta/2) (sharp_parameter ha) z=Λ.second/b^4) : z=y :=
    (Ghat_strictMono ha).injOn hz.le hy.1.le (he.trans hy.2.symm)
  exact ⟨ha,y,hy.1,hy.2,huniq,root_calibration ha hb (threshold Λ) hT⟩

end
end jacobi.RootMass
