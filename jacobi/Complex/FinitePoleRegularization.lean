import jacobi.Complex.SimplePole

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the finite simple-pole form of the residue theorem, obtained
here from divided differences and Cauchy--Goursat.
Use: finitePoleRegularization_analytic proves analyticity of this same function on the disk before finite_simple_residues applies Cauchy--Goursat.
-/
namespace jacobi.Complex
noncomputable section
open _root_.Complex Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual quotient after subtraction of its finite genuine principal parts, with the analytic removable values assigned at the poles.
Use: finitePoleRegularization_analytic proves analyticity of this same function on the disk before finite_simple_residues applies Cauchy--Goursat.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def finitePoleRegularization (g h : ℂ → ℂ) (S : Finset ℂ) (z : ℂ) : ℂ := by
  classical
  exact if z∈S then deriv (simplePoleNumerator g h z) z-
    ∑ p∈S.erase z,(g p/deriv h p)/(z-p)
  else g z/h z-∑ p∈S,(g p/deriv h p)/(z-p)

/-- Near each actual pole the globally regularized quotient equals its analytic divided-difference patch minus the other finite principal parts.
Use: finitePoleRegularization_analytic verifies the analytic extension across every member of the genuine finite pole set.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: exclude the other finitely many poles by a neighborhood. Away from the selected pole, split its summand from the finite sum and use the exact simple-pole subtraction identity; at the pole the assigned value is that same divided difference. -/
theorem finitePoleRegularization_eq_near (g h : ℂ → ℂ) (S : Finset ℂ) {p : ℂ}
    (hp : p∈S) (hh : h p=0) :
    finitePoleRegularization g h S =ᶠ[𝓝 p] fun z =>
      dslope (simplePoleNumerator g h p) p z-∑ q∈S.erase p,(g q/deriv h q)/(z-q) := by
  classical
  -- Finiteness supplies the neighborhood separating this pole from all the others.
  have hnear : (↑(S.erase p):Set ℂ)ᶜ∈𝓝 p :=
    (S.erase p).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hnear] with z hz
  by_cases he : z=p
  · subst z
    simp only [finitePoleRegularization,ite_eq_left hp,dslope_same]
  · have hn : z∉S := by
      intro h
      exact hz (Finset.mem_erase.mpr ⟨he,h⟩)
    rw [finitePoleRegularization,ite_eq_right hn,← Finset.sum_erase_add _ _ hp]
    rw [show g z/h z-((∑ q∈S.erase p,(g q/deriv h q)/(z-q))+(g p/deriv h p)/(z-p))=
      (g z/h z-(g p/deriv h p)/(z-p))-∑ q∈S.erase p,(g q/deriv h q)/(z-q) by ring]
    rw [simplePole_principal_part g h hh he]

/-- Away from its actual finite pole set, the global regularization is locally the literal quotient minus its principal parts.
Use: finitePoleRegularization_analytic handles all ordinary points and finite_simple_residues identifies the integrand on the original pole-free boundary circle.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the complement of the finite pole set is an open neighborhood of each such point. -/
theorem finitePoleRegularization_eq_off (g h : ℂ → ℂ) (S : Finset ℂ) {p : ℂ}
    (hp : p∉S) : finitePoleRegularization g h S =ᶠ[𝓝 p] fun z =>
      g z/h z-∑ q∈S,(g q/deriv h q)/(z-q) := by
  classical
  have hn : (↑S:Set ℂ)ᶜ∈𝓝 p := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hp
  filter_upwards [hn] with z hz
  exact ite_eq_right hz

/-- The finite principal-part regularization is analytic at every point where the quotient is ordinary or its characteristic denominator has an actual simple zero in the listed pole set.
Use: finite_simple_residues applies Cauchy--Goursat to this original regularized quotient over the whole closed disk.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: at a pole use the genuine analytic divided-difference patch. Elsewhere all denominators are nonzero. Each remaining principal part is analytic locally because its pole differs from the point being considered. -/
theorem finitePoleRegularization_analytic {g h : ℂ → ℂ} (S : Finset ℂ) {p : ℂ}
    (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p)
    (hzero : p∈S → h p=0 ∧ deriv h p≠0) (hregular : p∉S → h p≠0) :
    AnalyticAt ℂ (finitePoleRegularization g h S) p := by
  classical
  -- The two local formulas agree with the single globally defined regularization on an actual neighborhood.
  by_cases hp : p∈S
  · obtain ⟨h0,hd⟩ := hzero hp
    have hs : AnalyticAt ℂ (fun z : ℂ => ∑ q∈S.erase p,(g q/deriv h q)/(z-q)) p := by
      apply Finset.analyticAt_fun_sum
      intro q hq
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (Finset.mem_erase.mp hq).1.symm)
    exact ((simplePole_remainder_analytic hg hh hd).2.sub hs).congr
      (finitePoleRegularization_eq_near g h S hp h0).symm
  · have hs : AnalyticAt ℂ (fun z : ℂ => ∑ q∈S,(g q/deriv h q)/(z-q)) p := by
      apply Finset.analyticAt_fun_sum
      intro q hq
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (by intro he; exact hp (he ▸ hq)))
    exact ((hg.div hh (hregular hp)).sub hs).congr (finitePoleRegularization_eq_off g h S hp).symm

end
end jacobi.Complex
