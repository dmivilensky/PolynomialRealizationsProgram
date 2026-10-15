import «2610.05164v2».DualCertificate.CertificateAssembly

/-!
Article: 2610.05164v2, Theorem 3.6.
Joint continuity of the exact state faces as the positive ground parameter varies.
Use: `«2610.05164v2».DualCertificate.thetaPlus_joint_continuous` feeds
`«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` (face Criterion continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open Set «2610.05164v2».StateRegion.Scales
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Defines `FaceDomain` of type `` by `Ioi (0:ℝ) × Icc (0:ℝ) 1 × Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.V_joint_continuous` uses this definition to establish
continuity of the displayed function: `Continuous (fun p : FaceDomain => (scales
p.1.property).V p.2.1 p.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
abbrev FaceDomain := Ioi (0:ℝ) × Icc (0:ℝ) 1 × Icc (0:ℝ) 1

 /--
Continuity of the displayed function: `Continuous (fun p : FaceDomain => (scales
p.1.property).V p.2.1 p.2.2)`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.D_pos` with the
arguments shown in the proof.
-/
theorem V_joint_continuous : Continuous (fun p : FaceDomain => (scales p.1.property).V p.2.1 p.2.2) := by
  -- Establish continuity hk before using the function at limits or in calculus arguments.
  have hk : Continuous (fun p : FaceDomain => (p.1:ℝ)) := by fun_prop
  -- Establish continuity hu before using the function at limits or in calculus arguments.
  have hu : Continuous (fun p : FaceDomain => (p.2.1:ℝ)) := by fun_prop
  -- Establish continuity ht before using the function at limits or in calculus arguments.
  have ht : Continuous (fun p : FaceDomain => (p.2.2:ℝ)) := by fun_prop
  have hd : ∀ p : FaceDomain, (p.1:ℝ)+32+32-32*(p.2.1:ℝ)≠0 := fun p =>
    (scales p.1.property).D_pos p.2.1.property.2 |>.ne'
  unfold «2610.05164v2».StateRegion.Scales.V «2610.05164v2».StateRegion.Scales.f «2610.05164v2».StateRegion.Scales.k₀
    «2610.05164v2».StateRegion.Scales.D «2610.05164v2».StateRegion.Scales.k₁ scales
  fun_prop (disch := aesop)

 /--
Continuity of the displayed function: `Continuous (fun p : FaceDomain => (scales
p.1.property).yPlus p.2.1 p.2.2)`.

Use: `«2610.05164v2».DualCertificate.thetaMinus_joint_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (fun p : FaceDomain => (scales
p.1.property).thetaMinus p.2.1 p.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.yPlus_den_lower` with the arguments shown in the proof.
-/
theorem yPlus_joint_continuous : Continuous (fun p : FaceDomain => (scales p.1.property).yPlus p.2.1 p.2.2) := by
  have hk : Continuous (fun p : FaceDomain => (p.1:ℝ)) := by fun_prop
  have hu : Continuous (fun p : FaceDomain => (p.2.1:ℝ)) := by fun_prop
  have ht : Continuous (fun p : FaceDomain => (p.2.2:ℝ)) := by fun_prop
  have hd : ∀ p : FaceDomain, (p.1:ℝ)+32+32-32*(p.2.1:ℝ)*(p.2.2:ℝ)≠0 := fun p =>
    ((scales p.1.property).k₀_pos.trans_le ((scales p.1.property).yPlus_den_lower p.2.1.property p.2.2.property)).ne'
  unfold «2610.05164v2».StateRegion.Scales.yPlus «2610.05164v2».StateRegion.Scales.k₁ scales
  fun_prop (disch := aesop)

 /--
Continuity of the displayed function: `Continuous (fun p : FaceDomain => (scales
p.1.property).yMinus p.2.1 p.2.2)`.

Use: `«2610.05164v2».DualCertificate.thetaPlus_joint_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (fun p : FaceDomain => (scales
p.1.property).thetaPlus p.2.1 p.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.yMinus_den_lower` with the arguments shown in the proof.
-/
theorem yMinus_joint_continuous : Continuous (fun p : FaceDomain => (scales p.1.property).yMinus p.2.1 p.2.2) := by
  have hk : Continuous (fun p : FaceDomain => (p.1:ℝ)) := by fun_prop
  have hu : Continuous (fun p : FaceDomain => (p.2.1:ℝ)) := by fun_prop
  have ht : Continuous (fun p : FaceDomain => (p.2.2:ℝ)) := by fun_prop
  have hd : ∀ p : FaceDomain, (p.1:ℝ)+32+32*(p.2.2:ℝ)*(1-(p.2.1:ℝ))≠0 := fun p =>
    ((scales p.1.property).k₀_pos.trans_le ((scales p.1.property).yMinus_den_lower p.2.1.property.2 p.2.2.property.1)).ne'
  unfold «2610.05164v2».StateRegion.Scales.yMinus «2610.05164v2».StateRegion.Scales.k₀ «2610.05164v2».StateRegion.Scales.k₁ scales
  fun_prop (disch := aesop)

 /--
Continuity of the displayed function: `Continuous (fun p : FaceDomain => (scales
p.1.property).thetaMinus p.2.1 p.2.2)`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.yPlus_joint_continuous`,
`«2610.05164v2».StateRegion.Scales.E_pos`, `«2610.05164v2».StateRegion.Scales.yPlus_bounds`
with the arguments shown in the proof.
-/
theorem thetaMinus_joint_continuous : Continuous (fun p : FaceDomain => (scales p.1.property).thetaMinus p.2.1 p.2.2) := by
  have hk : Continuous (fun p : FaceDomain => (p.1:ℝ)) := by fun_prop
  have hu : Continuous (fun p : FaceDomain => (p.2.1:ℝ)) := by fun_prop
  have he : Continuous (fun p : FaceDomain => (scales p.1.property).E ((scales p.1.property).yPlus p.2.1 p.2.2)) :=
    hk.add (continuous_const.mul yPlus_joint_continuous)
  exact (hk.mul (continuous_const.sub hu)).div he (fun p =>
    ((scales p.1.property).E_pos ((scales p.1.property).yPlus_bounds p.2.1.property p.2.2.property).1).ne')

 /--
Continuity of the displayed function: `Continuous (fun p : FaceDomain => (scales
p.1.property).thetaPlus p.2.1 p.2.2)`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.yMinus_joint_continuous`,
`«2610.05164v2».StateRegion.Scales.E_pos`, `«2610.05164v2».StateRegion.Scales.yMinus_bounds`
with the arguments shown in the proof.
-/
theorem thetaPlus_joint_continuous : Continuous (fun p : FaceDomain => (scales p.1.property).thetaPlus p.2.1 p.2.2) := by
  have hk : Continuous (fun p : FaceDomain => (p.1:ℝ)) := by fun_prop
  have hu : Continuous (fun p : FaceDomain => (p.2.1:ℝ)) := by fun_prop
  have he : Continuous (fun p : FaceDomain => (scales p.1.property).E ((scales p.1.property).yMinus p.2.1 p.2.2)) :=
    hk.add (continuous_const.mul yMinus_joint_continuous)
  exact continuous_const.sub (((hk.add continuous_const).mul hu).div he (fun p =>
    ((scales p.1.property).E_pos (p.2.1.property.1.trans ((scales p.1.property).yMinus_bounds p.2.1.property p.2.2.property).1)).ne'))

end
end «2610.05164v2».DualCertificate
