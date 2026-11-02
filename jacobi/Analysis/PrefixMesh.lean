import jacobi.Analysis.BoundedMesh

/-!
Article: jacobi, Proposition C.3.
Source: dominated convergence and the reused original floor-mesh limit.
Use: prefix_mesh_limit identifies the dominated step-function limit with the literal source integral rather than an indicator expression.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory chebyshev1.Analysis
open scoped Topology

/-- Restricting a unit-interval integrand below a true physical prefix
endpoint gives exactly its original prefix integral.
Use: prefix_mesh_limit identifies the dominated step-function limit
with the literal source integral rather than an indicator expression.
Article: jacobi, Proposition C.3.
Proof: the cutoff intersects the original unit interval in (0,t);
the null endpoint does not affect the actual Lebesgue integral. -/
theorem unit_cutoff_integral (f:ℝ→ℝ) {t:ℝ} (ht:t∈Icc (0:ℝ) 1) :
    (∫ r in (0:ℝ)..1, if r<t then f r else 0)=∫ r in (0:ℝ)..t, f r := by
  -- Identify the actual restricted set; the only changed boundary is a null singleton.
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_of_le ht.1]
  have he : (fun r:ℝ => if r<t then f r else 0)=(Iio t).indicator f := rfl
  rw [he,integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio t ∩ Ioc (0:ℝ) 1=Ioo (0:ℝ) t := by
    ext r
    simp only [mem_inter_iff,mem_Iio,mem_Ioc,mem_Ioo]
    constructor
    · rintro ⟨h1,h0,_⟩
      exact ⟨h0,h1⟩
    · rintro ⟨h0,hr⟩
      exact ⟨hr,h0,hr.le.trans ht.2⟩
  rw [hs,restrict_Ioo_eq_restrict_Ioc]

/-- A uniformly bounded moving mesh prefix has the genuine original
continuum prefix integral as its limit, including a shrinking prefix.
Use: Cholesky GL quadrature and the target eigenvector Schur transform
pass actual growing sums to the source's physical spatial integrals.
Article: jacobi, Proposition C.3.
Proof: include the actual integer prefix cutoff in the finite mesh data.
Away from the single null limiting endpoint its indicator stabilizes,
by the true floor-mesh and physical endpoint limits. The established
bounded mesh theorem applies, and its integral is exactly the prefix. -/
theorem prefix_mesh_limit (n m:ℕ→ℕ) (a:ℕ→ℕ→ℝ) (f:ℝ→ℝ)
    (hn:Tendsto n atTop atTop) (hm:∀ᶠ r:ℕ in atTop,m r≤n r)
    {t B:ℝ} (ht:t∈Icc (0:ℝ) 1)
    (hmt:Tendsto (fun r:ℕ => (m r:ℝ)/(n r:ℝ)) atTop (𝓝 t))
    (hB:0≤B) (hb:∀ᶠ r:ℕ in atTop,∀j, |a r j|≤B)
    (hp:∀s∈Ioo (0:ℝ) 1,
      Tendsto (fun r => a r (Nat.floor ((n r:ℝ)*s))) atTop (𝓝 (f s))) :
    Tendsto (fun r => (∑j∈Finset.range (m r),a r j)/(n r:ℝ)) atTop
      (𝓝 (∫s in (0:ℝ)..t,f s)) := by
  -- Put the moving integer cutoff into the array before applying dominated convergence.
  classical
  let b (r j:ℕ) := if j<m r then a r j else 0
  have hbb : ∀ᶠ r:ℕ in atTop,∀j, |b r j|≤B := by
    filter_upwards [hb] with r hr
    intro j
    by_cases hj : j<m r <;> simp only [b,hj,ite_true,ite_false,abs_zero]
    · exact hr j
    · exact hB
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun r => b r (Nat.floor ((n r:ℝ)*s))) atTop
        (𝓝 (if s<t then f s else 0)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae (volume.ae_ne t)] with s hs hst
    have hfloor := floor_mesh_limit hn (tendsto_const_nhds (x:=s))
      (Eventually.of_forall (fun _ => hs.1.le))
    by_cases hlt : s<t
    · simp only [hlt,ite_true]
      apply (hp s hs).congr'
      filter_upwards [hfloor.eventually_lt hmt hlt,hn.eventually_gt_atTop 0] with r hr hnr
      have hnr' : (0:ℝ)<(n r:ℝ) := by exact_mod_cast hnr
      have hj : Nat.floor ((n r:ℝ)*s)<m r := by
        exact_mod_cast (div_lt_div_iff_of_pos_right hnr').mp hr
      simp only [b,hj,ite_true]
    · simp only [hlt,ite_false]
      have hgt : t<s := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hst)
      apply tendsto_const_nhds.congr'
      filter_upwards [hmt.eventually_lt hfloor hgt,hn.eventually_gt_atTop 0] with r hr hnr
      have hnr' : (0:ℝ)<(n r:ℝ) := by exact_mod_cast hnr
      have hj : ¬Nat.floor ((n r:ℝ)*s)<m r := by
        have hh : (m r:ℝ)<(Nat.floor ((n r:ℝ)*s):ℝ) :=
          (div_lt_div_iff_of_pos_right hnr').mp hr
        exact_mod_cast hh.not_gt
      simp only [b,hj,ite_false]
  have hh := bounded_mesh_limit n b (fun s => if s<t then f s else 0) hn hbb hpoint
  rw [unit_cutoff_integral f ht] at hh
  apply hh.congr'
  filter_upwards [hm] with r hr
  congr 1
  dsimp [b]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

end
end jacobi.Analysis
