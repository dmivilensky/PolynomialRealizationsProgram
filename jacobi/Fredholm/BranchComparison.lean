import jacobi.Fredholm.ParameterContinuity

/-!
Article: jacobi, Theorem D.7.
Actual endpoint continuity and strict mass-curve order compare arbitrary
interior and full-support candidates. The two printed alternatives
cannot both satisfy the same determinant target and mass bound.
Source: the intermediate value theorem and the verified envelope calculus.
Use: compares a constructed mass root with a smaller free-branch chi parameter.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original determinant has a strictly positive chi derivative at every interior physical pair.
Use: compares a constructed mass root with a smaller free-branch chi parameter.
Article: jacobi, Theorem D.7.
Proof: the third response is at most I3. Positive chi<1 and tau<=1
make the energy component strictly positive. The mass component is
nonnegative because g_e>=1/2, and the rational energy coefficient is positive. -/
theorem determinant_parameter_deriv_pos {t c : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) : 0<deriv (determinant t) c := by
  -- The sign uses only the actual derivatives and the original integrable moment bounds.
  rw [(determinant_parameter_envelope ht hc).deriv]
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hc' : c∈Icc (0:ℝ) 1 := ⟨hc.1.le,hc.2.le⟩
  have hi := (state_mean_bounds ht' hc').1
  have hr := response3_le ht' hc'
  have hratio : (1:ℝ)<3/(2*c) := (one_lt_div₀ (by linarith [hc.1])).mpr (by linarith [hc.2])
  have hri : t*response3 t c≤ i3 t c := by
    have h1 := mul_le_mul_of_nonneg_left hr ht.1.le
    have h2 := mul_le_mul_of_nonneg_right ht.2.le hi.le
    nlinarith
  have hB : 0<(3/(2*c))*i3 t c-(t/2)*response3 t c := by
    nlinarith [mul_pos (sub_pos.mpr hratio) hi]
  have hK : 0<envelopeCoefficient t c :=
    div_pos (mul_pos ht.1 (sq_pos_of_pos hc.1)) (sub_pos.mpr hc.2)
  have he := (parameter_bounds ⟨ht.1,ht.2.le⟩ hc).2.1
  have hmass := (massGradient_pos ht hc).2
  have hpos := mul_pos hK hB
  have hnon : 0≤(2*edge t c-1)*((3/2:ℝ)*(i2 t c-c*t/2*response2 t c)) :=
    mul_nonneg (by linarith) hmass.le
  linarith

/-- At any fixed interior shape the actual determinant strictly increases throughout physical chi.
Use: brackets determinant values while moving along the actual constant-mass curve.
Article: jacobi, Theorem D.7.
Proof: the original determinant has its genuine strictly positive
ordinary derivative; apply the mean-value theorem on (0,1). -/
theorem determinant_parameter_strictMono {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    StrictMonoOn (determinant t) (Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro c hc
    exact (determinant_parameter_envelope ht hc).continuousAt.continuousWithinAt
  · intro c hc
    exact determinant_parameter_deriv_pos ht (interior_subset hc)

/-- Every shape to the right of an interior mass root has a genuine physical root above any free candidate of no greater mass.
Use: compares the original two Fredholm branches without assuming a mass graph at the full-support boundary.
Article: jacobi, Theorem D.7.
Proof: the lower chi value has mass at most the target by shape
monotonicity. Chi=1 has strictly larger mass than the target. Closed
continuity and the intermediate value theorem give a root, whose strict
upper mass inequality excludes chi=1. -/
theorem mass_root_to_right {t u c k : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (htu : t<u) (hm : mass 1 k≤mass t c) :
    ∃ w : ℝ,w∈Ioo (0:ℝ) 1 ∧ k≤w ∧ mass u w=mass t c := by
  -- The upper bracket uses the already verified closed chi boundary, not an assumed divergent mass.
  have hlo : mass u k≤mass t c :=
    ((mass_shape_strictMono ⟨hk.1,hk.2.le⟩).monotoneOn
      ⟨hu.1.le,hu.2.le⟩ (by norm_num) hu.2.le).trans hm
  have hhi : mass t c<mass u 1 := by
    have h1 := mass_parameter_strictMono ⟨ht.1.le,ht.2.le⟩ ⟨hc.1.le,hc.2.le⟩
      (by norm_num : (1:ℝ)∈Icc 0 1) hc.2
    have h2 := (mass_shape_strictMono (by norm_num : (1:ℝ)∈Ioc 0 1)).monotoneOn
      ⟨ht.1.le,ht.2.le⟩ ⟨hu.1.le,hu.2.le⟩ htu.le
    exact h1.trans_le h2
  obtain ⟨w,hw,he⟩ := intermediate_value_Icc hk.2.le
    ((mass_parameter_continuous ⟨hu.1.le,hu.2.le⟩).mono
      (fun _ hw => ⟨hk.1.le.trans hw.1,hw.2⟩)) ⟨hlo,hhi.le⟩
  have hw1 : w<1 := lt_of_le_of_ne hw.2 (by
    intro h
    rw [← h,he] at hhi
    exact (lt_irrefl _ hhi))
  exact ⟨w,⟨hk.1.trans_le hw.1,hw1⟩,hw.1,he⟩

/-- The actual free determinant is at most the determinant of any interior candidate with at least its mass.
Use: the endpoint comparison required for mutual exclusion of the printed alternatives.
Article: jacobi, Theorem D.7.
Proof: at every interior shape sufficiently near one construct the
actual same-mass root. Strict mass-curve decrease and fixed-shape chi
monotonicity bound the free chi value there. Pass to one using dominated
continuity of the original determinant, without differentiating at that boundary. -/
theorem free_determinant_le_interior {t c k : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (hm : mass 1 k≤mass t c) : determinant 1 k≤determinant t c := by
  -- Only the true fixed-chi endpoint limit is needed for this comparison.
  have hle : 𝓝[<] (1:ℝ)≤𝓝[Icc (0:ℝ) 1] 1 :=
    le_inf inf_le_left (le_principal_iff.mpr (Icc_mem_nhdsLT (by norm_num : (0:ℝ)<1)))
  have hlim := ((determinant_shape_continuous ⟨hk.1.le,hk.2⟩) 1
    (by norm_num : (1:ℝ)∈Icc 0 1)).tendsto.mono_left hle
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT ht.2] with u hu
  have hup : u∈Ioo (0:ℝ) 1 := ⟨ht.1.trans hu.1,hu.2⟩
  obtain ⟨w,hw,hkw,he⟩ := mass_root_to_right ht hup hc hk hu.1 hm
  exact ((determinant_parameter_strictMono hup).monotoneOn hk hw hkw).trans
    (determinant_mass_level_order ht hup hc hw hu.1 he.symm).le

/-- The actual free determinant is strictly below every interior candidate whose mass is at least its own.
Use: rules out simultaneous admissibility of the two printed branches and identifies all candidate values with the actual minimum.
Article: jacobi, Theorem D.7.
Proof: insert one genuine intermediate same-mass root. The weak
endpoint comparison bounds the free value by this intermediate value;
strict interior mass-curve decrease then separates it from the initial candidate. -/
theorem free_determinant_lt_interior {t c k : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) (hk : k∈Ioo (0:ℝ) 1)
    (hm : mass 1 k≤mass t c) : determinant 1 k<determinant t c := by
  -- A fixed intermediate point preserves strictness when taking the final endpoint limit.
  let u := (1+t)/2
  have hu : u∈Ioo (0:ℝ) 1 := by dsimp [u]; constructor <;> linarith [ht.1,ht.2]
  have htu : t<u := by dsimp [u]; linarith [ht.2]
  obtain ⟨w,hw,_,he⟩ := mass_root_to_right ht hu hc hk htu hm
  have hweak := free_determinant_le_interior hu hw hk (by rwa [he])
  exact hweak.trans_lt (determinant_mass_level_order ht hu hc hw htu he.symm)

end
end jacobi.Fredholm
