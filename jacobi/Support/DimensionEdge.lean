import jacobi.Support.EdgeLimit
import jacobi.Reference.JointContinuity
import jacobi.Analysis.DimensionRatio

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The full complex edge limit in the true matrix dimension n+1, in both
the polynomial normalization and the spatial coordinate. This removes
the degree/dimension shift and includes the complete middle row.
Use: the full original Gram–Cholesky and eigenvector limits use the same matrix-size coordinates as the source continuum operators, including the actual middle index.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The genuine support-polynomial complex edge limit holds with exactly the original matrix-size normalization, spatial mesh and complete matrix half-chain range.
Use: the full original Gram–Cholesky and eigenvector limits use the same matrix-size coordinates as the source continuum operators, including the actual middle index.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: along every moving physical half mesh, the proved degree-normalized wave converges to the genuine reference solution. The actual ratio (n+1)/n tends to one, so its real-power normalization changes no limit, and either original spatial coordinate tends to the same point. Joint continuity of the actual reference solution covers zero as well. The full matrix half-mesh compactness criterion makes the resulting matrix-size error uniform. -/
theorem naturalWave_dimension_edge {a b:ℝ} (ha:-1<a) (hb:-1<b) {z:ℕ→ℂ} {E:ℂ}
    (hz:Tendsto z atTop (𝓝 E)) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,2*m≤n+1→
      ‖((((n:ℝ)+1)^(-gamma a):ℝ):ℂ)*naturalWave a b ha hb n m
          (1-z n/(2*(jacobi.Jacobi.frequency a b (n+1):ℂ)^2))-
        (topConstant a b:ℂ)*((π^gamma a:ℝ):ℂ)*
          solution a (E+(jacobi.Jacobi.endpointCorrection a:ℂ)) ((m:ℝ)/((n:ℝ)+1))‖<ε := by
  -- First prove the exact matrix-size limit along every actual moving physical mesh.
  refine jacobi.Analysis.half_mesh_uniform_zero (fun n m =>
    ((((n:ℝ)+1)^(-gamma a):ℝ):ℂ)*naturalWave a b ha hb n m
      (1-z n/(2*(jacobi.Jacobi.frequency a b (n+1):ℂ)^2))-
      (topConstant a b:ℂ)*((π^gamma a:ℝ):ℂ)*
        solution a (E+(jacobi.Jacobi.endpointCorrection a:ℂ)) ((m:ℝ)/((n:ℝ)+1))) ?_
  intro ns ms t ht hn hm hhalf
  let A : ℂ := (topConstant a b:ℂ)*((π^gamma a:ℝ):ℂ)
  let Z : ℂ := E+(jacobi.Jacobi.endpointCorrection a:ℂ)
  let y (n:ℕ) : ℂ := 1-z n/(2*(jacobi.Jacobi.frequency a b (n+1):ℂ)^2)
  have hsol : ContinuousAt (fun u:ℝ => solution a Z u) t := by
    have hpair : ContinuousAt (fun u:ℝ => (u,Z)) t := continuousAt_id.prodMk continuousAt_const
    have hJ : ContinuousAt (fun p:ℝ × ℂ => solution a p.2 p.1) (t,Z) :=
      solution_joint_continuous ha ⟨ht.1,by linarith [ht.2]⟩ Z
    simpa only [Function.comp_def] using hJ.comp (f:=fun u:ℝ => (u,Z)) hpair
  have herror : Tendsto (fun k => (((ns k:ℝ)^(-gamma a):ℝ):ℂ)*
      naturalWave a b ha hb (ns k) (ms k) (y (ns k))-
      A*solution a Z ((ms k:ℝ)/(ns k:ℝ))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := naturalWave_complex_edge ha hb hz ε hε
    filter_upwards [hn.eventually_ge_atTop N] with k hk
    simpa only [dist_eq_norm,sub_zero,A,Z,y] using hN (ns k) hk (ms k) (hhalf k)
  have hdegree := herror.add ((hsol.tendsto.comp hm).const_mul A)
  simp only [Function.comp_def,sub_add_cancel,zero_add] at hdegree
  -- The only normalization change is a positive real power of the exact dimension/degree ratio.
  have hscale : Tendsto (fun k => ((ns k:ℝ)+1)/(ns k:ℝ)) atTop (𝓝 1) := by
    exact jacobi.Analysis.successor_ratio_tendsto hn
  have hp := hscale.rpow_const (p:=-gamma a) (Or.inl one_ne_zero)
  simp only [one_rpow] at hp
  have hpC := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  have hvalue : Tendsto (fun k => ((((ns k:ℝ)+1)^(-gamma a):ℝ):ℂ)*
      naturalWave a b ha hb (ns k) (ms k) (y (ns k))) atTop (𝓝 (A*solution a Z t)) := by
    have h := hpC.mul hdegree
    simp only [Complex.ofReal_one,one_mul] at h
    apply (tendsto_congr' ?_).mpr h
    filter_upwards [hn.eventually_gt_atTop 0] with k hk
    have hn0 : (0:ℝ)<ns k := by exact_mod_cast hk
    have he : (((((ns k:ℝ)+1)/(ns k:ℝ))^(-gamma a)*(ns k:ℝ)^(-gamma a):ℝ):ℂ)=
        ((((ns k:ℝ)+1)^(-gamma a):ℝ):ℂ) := by
      congr 1
      rw [Real.div_rpow (by positivity : (0:ℝ)≤(ns k:ℝ)+1) hn0.le]
      field_simp [(rpow_pos_of_pos hn0 (-gamma a)).ne']
    change ((((ns k:ℝ)+1)^(-gamma a):ℝ):ℂ)*naturalWave a b ha hb (ns k) (ms k) (y (ns k))=
      (((((ns k:ℝ)+1)/(ns k:ℝ))^(-gamma a):ℝ):ℂ)*
        ((((ns k:ℝ)^(-gamma a):ℝ):ℂ)*naturalWave a b ha hb (ns k) (ms k) (y (ns k)))
    rw [← mul_assoc,← Complex.ofReal_mul,he]
  have hmesh : Tendsto (fun k => (ms k:ℝ)/((ns k:ℝ)+1)) atTop (𝓝 t) := by
    exact jacobi.Analysis.degree_to_size_mesh hn hm
  -- Both spatial meshes approach the same original physical point, including the zero endpoint.
  simpa only [sub_self,A,Z,y,Function.comp_def] using
    hvalue.sub ((hsol.tendsto.comp hmesh).const_mul A)

end
end jacobi.Support
