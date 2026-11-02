import jacobi.Fredholm.ParameterEndpoints

/-!
Article: jacobi, Theorem D.7.
Every physical pair has a strictly feasible positive Fredholm target at
its actual mass. The scalar concentrated endpoint is approached through
genuine mass roots of the original quadratures, including full support.
Source: actual mass monotonicity, the envelope and the exact tau=0 endpoint.
Use: compares the actual determinant to its exact concentrated scalar endpoint.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Every interior same-mass root can be continued to each smaller positive shape with chi bounded by the scalar mass.
Use: compares the actual determinant to its exact concentrated scalar endpoint.
Article: jacobi, Theorem D.7.
Proof: increasing shape strictly increases mass, so chi is below its
actual mass. At a smaller shape, the original chi and the scalar mass
bracket the desired mass. Closed continuity gives a genuine physical root. -/
theorem mass_root_to_left {t v c M : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hv : v∈Ioo (0:ℝ) t)
    (hc : c∈Ioo (0:ℝ) 1) (hM : M<1) (hm : mass t c=M) :
    ∃ w : ℝ,w∈Ioo (0:ℝ) 1 ∧ w≤M ∧ mass v w=M := by
  -- The upper bracket is finite and lies strictly below the actual chi pole.
  have hcm : c<M := by
    have hh := mass_shape_strictMono ⟨hc.1,hc.2.le⟩
      (by norm_num : (0:ℝ)∈Icc 0 1) ⟨ht.1.le,ht.2.le⟩ ht.1
    change mass 0 c<mass t c at hh
    rwa [(zero_shape c).1,hm] at hh
  have hMp : M∈Ioc (0:ℝ) 1 := ⟨hc.1.trans hcm,hM.le⟩
  have hvp : v∈Ioo (0:ℝ) 1 := ⟨hv.1,hv.2.trans ht.2⟩
  have hlo : mass v c≤M := by
    rw [← hm]
    exact (mass_shape_strictMono ⟨hc.1,hc.2.le⟩).monotoneOn
      ⟨hvp.1.le,hvp.2.le⟩ ⟨ht.1.le,ht.2.le⟩ hv.2.le
  have hhi : M<mass v M := by
    have hh := mass_shape_strictMono hMp (by norm_num : (0:ℝ)∈Icc 0 1)
      ⟨hvp.1.le,hvp.2.le⟩ hvp.1
    dsimp only at hh
    rwa [(zero_shape M).1] at hh
  obtain ⟨w,hw,he⟩ := intermediate_value_Icc hcm.le
    ((mass_parameter_continuous ⟨hvp.1.le,hvp.2.le⟩).mono
      (fun _ hw => ⟨hc.1.le.trans hw.1,hw.2.trans hM.le⟩)) ⟨hlo,hhi.le⟩
  exact ⟨w,⟨hc.1.trans_le hw.1,hw.2.trans_lt hM⟩,hw.2,he⟩

/-- An interior candidate determinant is at most its genuine concentrated scalar endpoint at the same mass.
Use: a strict version follows by inserting an actual intermediate mass root.
Article: jacobi, Theorem D.7.
Proof: for every smaller positive shape construct the actual mass root.
Its determinant exceeds the given one by the complete mass-curve order,
but is at most the fixed-chi scalar-mass determinant there. Pass to zero
using actual dominated shape continuity and the exact scalar endpoint. -/
theorem determinant_le_scalar {t c : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) (hM : mass t c<1) :
    determinant t c≤-log (1-mass t c)-mass t c := by
  -- Only a fixed-chi endpoint limit is taken; no regularity of an inverse family at zero is presumed.
  have hmpos := mass_pos ⟨ht.1.le,ht.2.le⟩ ⟨hc.1,hc.2.le⟩
  have hMp : mass t c∈Ico (0:ℝ) 1 := ⟨hmpos.le,hM⟩
  have hle : 𝓝[>] (0:ℝ)≤𝓝[Icc (0:ℝ) 1] 0 :=
    le_inf inf_le_left (le_principal_iff.mpr (Icc_mem_nhdsGT (by norm_num : (0:ℝ)<1)))
  have hlim := ((determinant_shape_continuous hMp) 0
    (by norm_num : (0:ℝ)∈Icc 0 1)).tendsto.mono_left hle
  rw [(zero_shape (mass t c)).2] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT ht.1] with v hv
  obtain ⟨w,hw,hwM,he⟩ := mass_root_to_left ht hv hc hM rfl
  have hvp : v∈Ioo (0:ℝ) 1 := ⟨hv.1,hv.2.trans ht.2⟩
  exact (determinant_mass_level_order hvp ht hw hc hv.2 he).le.trans
    ((determinant_parameter_strictMono hvp).monotoneOn hw ⟨hmpos,hM⟩ hwM)

/-- Every interior candidate determinant is strictly below the concentrated scalar threshold at its actual mass below one.
Use: discharges strict feasibility of the direct method for all interior physical parameters.
Article: jacobi, Theorem D.7.
Proof: insert a genuine same-mass root at half the shape. Its determinant
strictly exceeds the original one and is bounded by the exact scalar endpoint. -/
theorem determinant_lt_scalar_interior {t c : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) (hM : mass t c<1) :
    determinant t c< -log (1-mass t c)-mass t c := by
  -- A fixed intermediate point preserves the strict inequality before passing to the scalar endpoint.
  have hv : t/2∈Ioo (0:ℝ) t := by constructor <;> linarith [ht.1]
  have hvp : t/2∈Ioo (0:ℝ) 1 := ⟨hv.1,hv.2.trans ht.2⟩
  obtain ⟨w,hw,_,he⟩ := mass_root_to_left ht hv hc hM rfl
  have hweak := determinant_le_scalar hvp hw (by rwa [he])
  rw [he] at hweak
  exact (determinant_mass_level_order hvp ht hw hc hv.2 he).trans_le hweak

/-- Every positive subunit mass occurs at every positive interior shape with a physical chi.
Use: compares a full-support candidate to an actual interior mass root.
Article: jacobi, Theorem D.7.
Proof: chi=0 has zero mass, while chi=M has strictly larger mass
than M by the exact zero-shape endpoint and strict shape increase.
Continuity gives a root, with strict bracketing excluding chi=0. -/
theorem interior_mass_root {t M : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hM : M∈Ioo (0:ℝ) 1) :
    ∃ c : ℝ,c∈Ioo (0:ℝ) 1 ∧ mass t c=M := by
  -- The scalar mass itself supplies a finite physical upper chi bracket.
  have hup : M<mass t M := by
    have hh := mass_shape_strictMono ⟨hM.1,hM.2.le⟩ (by norm_num : (0:ℝ)∈Icc 0 1)
      ⟨ht.1.le,ht.2.le⟩ ht.1
    dsimp only at hh
    rwa [(zero_shape M).1] at hh
  obtain ⟨c,hc,he⟩ := intermediate_value_Icc hM.1.le
    ((mass_parameter_continuous ⟨ht.1.le,ht.2.le⟩).mono
      (fun _ hc => ⟨hc.1,hc.2.trans hM.2.le⟩))
    (show M∈Icc (mass t 0) (mass t M) by rw [(zero_parameter t).1]; exact ⟨hM.1.le,hup.le⟩)
  have hc0 : 0<c := lt_of_le_of_ne hc.1 (by
    intro h
    rw [← h,(zero_parameter t).1] at he
    exact hM.1.ne he)
  exact ⟨c,⟨hc0,hc.2.trans_lt hM.2⟩,he⟩

/-- The actual determinant of every physical candidate is strictly below the concentrated scalar threshold when its mass is below one.
Use: handles full support without assuming an ordinary shape derivative beyond tau=1.
Article: jacobi, Theorem D.7.
Proof: the interior case is the actual mass-curve endpoint comparison.
In the free case construct a genuine interior root of the same subunit
mass. The strict branch comparison puts the free value below that
interior value, which is strictly below the scalar threshold. -/
theorem determinant_lt_scalar {t c : ℝ}
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) (hM : mass t c<1) :
    determinant t c< -log (1-mass t c)-mass t c := by
  -- This proves the exact missing feasibility inequality before invoking optimizer existence.
  rcases lt_or_eq_of_le ht.2 with hti | hte
  · exact determinant_lt_scalar_interior ⟨ht.1,hti⟩ hc hM
  · subst t
    have hpos := mass_pos (by norm_num : (1:ℝ)∈Icc 0 1) ⟨hc.1,hc.2.le⟩
    obtain ⟨k,hk,he⟩ := interior_mass_root (by norm_num : (1/2:ℝ)∈Ioo 0 1) ⟨hpos,hM⟩
    have h1 := free_determinant_lt_interior (by norm_num : (1/2:ℝ)∈Ioo 0 1) hk hc (by rw [he])
    have h2 := determinant_lt_scalar_interior (by norm_num : (1/2:ℝ)∈Ioo 0 1) hk (by rwa [he])
    rw [he] at h2
    exact h1.trans h2

/-- Every physical parameter pair defines a strictly feasible positive-mass Fredholm variational problem.
Use: constructs actual profiles for arbitrary printed pairs through the already proved direct method.
Article: jacobi, Theorem D.7.
Proof: at mass at least one the concentrated scalar threshold is
infinite. Below one it is the exact scalar logarithm, and the proved
strict endpoint comparison applies. The determinant is positive, so
its real value embeds strictly monotonically in the extended nonnegative reals. -/
theorem candidate_strict_feasibility {t c : ℝ}
    (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    ENNReal.ofReal (determinant t c)<fredholmTerm 1 (mass t c) := by
  -- The scalar pole and finite branch use the same original actual mass.
  by_cases hM : mass t c<1
  · rw [fredholmTerm,ite_eq_right (by simpa only [one_mul] using not_le.mpr hM)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by
      have hh := determinant_lt_scalar ht hc hM
      have hp := determinant_pos ht hc
      unfold fredholmLog
      simp only [one_mul]
      linarith)).mpr
    simpa only [fredholmLog,one_mul] using determinant_lt_scalar ht hc hM
  · rw [fredholmTerm,ite_eq_left (by simpa only [one_mul] using not_lt.mp hM)]
    exact ENNReal.ofReal_lt_top

end
end jacobi.Fredholm
