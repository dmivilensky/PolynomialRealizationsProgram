import jacobi.Reference.SpectralAnalytic

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The actual square-root-free energy series converges normally on every
compact product inside its spatial disk. This proves joint continuity
of the original reference function, including the singular spatial endpoint
and the spectral square-root branch point.
Use: proves joint continuity of the genuine original f(t,z) and permits uniform compact-parameter integration in GL.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original reference energy core is jointly continuous in energy and spatial hypergeometric argument throughout its disk.
Use: proves joint continuity of the genuine original f(t,z) and permits uniform compact-parameter integration in GL.
Article: jacobi, Lemma C.1.
Proof: enclose the spatial argument in a smaller disk of radius less
than one. On a product with a fixed energy disk, the actual coefficient
bound gives one summable positive-parameter 2F1 majorant. Continuous
polynomial terms therefore have a jointly continuous sum. -/
theorem energyCore_joint_continuous (a : ℝ) (z x : ℂ) (hx : ‖x‖<1) :
    ContinuousAt (fun p : ℂ × ℂ => energyCore a p.1 p.2) (z,x) := by
  -- Both variables vary in the same actual normally convergent series.
  obtain ⟨D,hD,hbound⟩ := energyCoefficient_bound a z
  let r : ℝ := (‖x‖+1)/2
  have hr0 : 0<r := by dsimp [r]; positivity
  have hxr : ‖x‖<r := by dsimp [r]; linarith
  have hr1 : r<1 := by dsimp [r]; linarith
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n‖*r^n
  have hM : Summable M := by
    have hh := Hypergeometric.summable_norm (u := (D:ℂ)) (v := (D:ℂ))
      (c := ((gamma a:ℂ)+1/2)) (x := (r:ℂ)) (by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0]
        exact hr1)
    convert hh using 1
    funext n
    dsimp only [M]
    rw [norm_mul (ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n)]
    congr 1
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0]
  have hc (n : ℕ) : Continuous (fun p : ℂ × ℂ => energyCoefficient a n p.1*p.2^n) := by
    have hh : Continuous (energyCoefficient a n) :=
      continuous_iff_continuousAt.mpr (fun w => (energyCoefficient_analytic a n w).continuousAt)
    exact (hh.comp continuous_fst).mul (continuous_snd.pow n)
  have hh := continuousOn_tsum (s := Metric.ball z 1×ˢMetric.ball (0:ℂ) r)
    (fun n => (hc n).continuousOn) hM (fun n p hp => by
      change ‖energyCoefficient a n p.1*p.2^n‖≤_
      rw [norm_mul,norm_pow]
      apply mul_le_mul (hbound p.1 hp.1 n) ?_ (by positivity) (norm_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (by
        simpa only [Metric.mem_ball,dist_zero_right] using hp.2)) n)
  exact hh.continuousAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
    ⟨Metric.mem_ball_self (by norm_num),by simpa only [Metric.mem_ball,dist_zero_right] using hxr⟩)

/-- Every physical spatial reference coordinate, including the left endpoint, lies inside the actual complex hypergeometric disk.
Use: applies the jointly continuous original energy series at t=0 as well as throughout 0<t<1.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: the positive interior case was proved from strict cosine monotonicity; at zero the actual coordinate is zero. -/
theorem coordinate_norm_lt_one_of_nonneg {t : ℝ} (ht : t∈Ico 0 1) :
    ‖(coordinate t:ℂ)‖<1 := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    rw [coordinate_properties.1,Complex.ofReal_zero,norm_zero]
    norm_num
  · exact coordinate_norm_lt_one ⟨h,ht.2⟩

/-- The genuine source reference solution is jointly continuous in space and complex energy, including its singular endpoint t=0.
Use: justifies the original continuous kernel summands and compact-parameter endpoint arguments in the GL construction.
Article: jacobi, Lemma C.1.
Proof: use the actual square-root-free energy series. Its jointly
continuous core is composed with the genuine continuous cosine
coordinate; the actual sine-power prefactor is continuous throughout
the full admissible order range. -/
theorem solution_joint_continuous {a : ℝ} (ha : -1<a) {t : ℝ}
    (ht : t∈Ico 0 1) (z : ℂ) :
    ContinuousAt (fun p : ℝ × ℂ => solution a p.2 p.1) (t,z) := by
  -- This also covers z=c_0alpha; no branch continuity is required.
  have hcoord : Continuous coordinate :=
    continuous_iff_continuousAt.mpr (fun s => (coordinate_hasDerivAt s).continuousAt)
  have hpair : ContinuousAt (fun p : ℝ × ℂ => (p.2,(coordinate p.1:ℂ))) (t,z) :=
    continuousAt_snd.prodMk ((Complex.continuous_ofReal.comp
      (hcoord.comp continuous_fst)).continuousAt)
  have hc := (energyCore_joint_continuous a z (coordinate t:ℂ)
    (coordinate_norm_lt_one_of_nonneg ht)).comp_of_eq hpair rfl
  have hw : ContinuousAt (fun p : ℝ × ℂ => (weight a p.1:ℂ)) (t,z) :=
    Complex.continuous_ofReal.continuousAt.comp ((weight_properties ha).1.continuousAt.comp continuousAt_fst)
  have he : (fun p : ℝ × ℂ => solution a p.2 p.1)=
      (fun p => (weight a p.1:ℂ)*energyCore a p.2 (coordinate p.1:ℂ)) :=
    funext fun p => solution_eq_energy_series a p.2 p.1
  rw [he]
  exact hw.mul hc

end
end jacobi.Reference
