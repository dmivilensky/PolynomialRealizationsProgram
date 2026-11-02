import jacobi.Support.NormalizedMeshLimit
import jacobi.Analysis.HalfMeshCompactness

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The genuine reference core has a uniformly vanishing residual in the
actual finite ground-normalized Volterra equation at every convergent
complex scaled energy. The actual bounded kernel limit, including
zero and moving endpoints, discharges the continuum approximation.
Use: edgeResidual and the normalized complex edge theorem retain the precise energy factor in the original finite Volterra equation.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual complex spectral displacement multiplied by the square of the original degree.
Use: edgeResidual and the normalized complex edge theorem retain the precise energy factor in the original finite Volterra equation.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def groundScaledEnergy (a b:ℝ) (n:ℕ) (y:ℂ) : ℂ :=
  (n:ℂ)^2*(y-(cos (gamma a*step a b (n+1)):ℝ))

/-- The residual of the genuine continuum reference core in the actual normalized finite support equation.
Use: edgeResidual_uniform supplies the concrete vanishing forcing in the finite Gronwall proof of complex polynomial convergence.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def edgeResidual (a b:ℝ) (ha:-1<a) (hb:-1<b) (z y:ℂ) (n m:ℕ) : ℂ :=
  regularWave a z ((m:ℝ)/(n:ℝ))-1-
    groundScaledEnergy a b n y*finiteGroundMesh a b ha hb n m (regularWave a z)

/-- The genuine continuum reference solution has uniformly vanishing residual in the actual finite normalized equation at every convergent complex scaled energy.
Use: naturalWave_normalized_edge applies finite nested Volterra stability to the actual support polynomials, with this fully proved residual rather than an assumed approximation certificate.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: along every moving half mesh, the true reference core is continuous and the actual finite operator tends to twice groundVolterra. The actual scaled energy tends to half the continuum displacement, so the limiting residual is zero by the proved reference equation. Compactness of the original closed half interval makes this convergence uniform over all original mesh indices. -/
theorem edgeResidual_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b) (z:ℂ) (y:ℕ→ℂ)
    (hy:Tendsto (fun n => groundScaledEnergy a b n (y n)) atTop
      (𝓝 (((eigenvalue a 0:ℂ)-z)/2))) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,2*m≤n+1→‖edgeResidual a b ha hb z (y n) n m‖<ε := by
  -- The compactness criterion is applied to the same actual residual at every original mesh point.
  apply jacobi.Analysis.half_mesh_uniform_zero
  intro ns ms t ht hn hm hhalf
  have hq : Tendsto (fun i => regularWave a z ((ms i:ℝ)/(ns i:ℝ))) atTop (𝓝 (regularWave a z t)) :=
    (regularWave_analytic a z ⟨ht.1,by linarith [ht.2]⟩).continuousAt.tendsto.comp hm
  have hmesh := finiteGroundMesh_limit ha hb hn hm (Eventually.of_forall hhalf) ht
    (regularWave_continuous_half a z)
  have hlim := (hq.sub_const 1).sub ((hy.comp hn).mul hmesh)
  have hz : regularWave a z t-1-(((eigenvalue a 0:ℂ)-z)/2)*(2*groundVolterra a (regularWave a z) t)=0 := by
    rw [regularWave_groundVolterra ha z ht]
    ring
  simpa only [edgeResidual,Function.comp_def,hz] using hlim

end
end jacobi.Support
