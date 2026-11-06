import nesterov.Flow.Continuation
import nesterov.Flow.Lyapunov

/-!
Article: §3, well-posedness on the full half-line.
Use: bounded-set Lipschitz gradients and the mechanical energy identity give
uniform local continuation in the actual (possibly infinite-dimensional) Hilbert space.
-/
namespace nesterov.Flow
noncomputable section
open Set Metric Filter
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem Objective.vectorField_lipschitz_bounded {m θ : ℝ} {f : E→ℝ}
    (hf : Objective m f) (R : ℝ) : ∃ K : NNReal,
    LipschitzOnWith K (vectorField θ f) (closedBall 0 R) := by
  obtain ⟨K,hK⟩ := hf.gradient_lipschitz_bounded R
  refine ⟨1+‖θ‖₊+K,LipschitzOnWith.of_dist_le_mul (fun z hz w hw => ?_)⟩
  have hz' : z.1∈closedBall (0:E) R := by
    rw [mem_closedBall_zero_iff] at hz ⊢
    exact (norm_fst_le z).trans hz
  have hw' : w.1∈closedBall (0:E) R := by
    rw [mem_closedBall_zero_iff] at hw ⊢
    exact (norm_fst_le w).trans hw
  have hg := hK.norm_sub_le hz' hw'
  have hx := norm_fst_le (z-w)
  have hv := norm_snd_le (z-w)
  simp only [Prod.fst_sub,Prod.snd_sub] at hx hv
  rw [dist_eq_norm,dist_eq_norm]
  change max ‖z.2-w.2‖ ‖(-θ • z.2-gradient f z.1)-(-θ • w.2-gradient f w.1)‖≤_
  have hcoeff : (↑(1+‖θ‖₊+K):ℝ)=1+|θ|+K := by simp
  rw [hcoeff]
  apply max_le
  · nlinarith [abs_nonneg θ, K.coe_nonneg, norm_nonneg (z-w)]
  · have he : (-θ • z.2-gradient f z.1)-(-θ • w.2-gradient f w.1)=
        -θ • (z.2-w.2)-(gradient f z.1-gradient f w.1) := by module
    rw [he]
    apply (norm_sub_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_neg]
    nlinarith [mul_le_mul_of_nonneg_left hv (abs_nonneg θ),
      mul_le_mul_of_nonneg_left hx K.coe_nonneg,norm_nonneg (z-w)]

theorem Objective.energy_nonneg {m : ℝ} {f : E→ℝ} (hf : Objective m f) (z : E×E) :
    0≤energy f z.1 z.2 := by
  have hh := hf.quadratic_lower z.1
  dsimp [energy]
  nlinarith [hf.m_pos,sq_nonneg ‖z.1‖,sq_nonneg ‖z.2‖]

/-- A bounded energy sublevel lies in a bounded state ball. -/
theorem Objective.energy_sublevel_bounded {m : ℝ} {f : E→ℝ} (hf : Objective m f)
    {e : ℝ} (he : 0≤e) :
    ∃ R : ℝ,0<R ∧ ∀ z : E×E,energy f z.1 z.2≤e → ‖z‖≤R := by
  let R : ℝ := 2+2*e/m+2*e
  have hm := hf.m_pos
  have hR : 0<R := by dsimp [R]; positivity
  refine ⟨R,hR,fun z hz => ?_⟩
  have hl := hf.quadratic_lower z.1
  have hx : ‖z.1‖^2≤2*e/m := by
    apply (le_div_iff₀ hm).mpr
    dsimp [energy] at hz
    nlinarith [sq_nonneg ‖z.2‖]
  have hv : ‖z.2‖^2≤2*e := by
    dsimp [energy] at hz
    nlinarith [mul_nonneg (show 0≤m/2 by positivity) (sq_nonneg ‖z.1‖)]
  rw [Prod.norm_def]
  apply max_le <;> dsimp [R]
  · nlinarith [sq_nonneg (‖z.1‖-1),div_nonneg he hm.le]
  · nlinarith [sq_nonneg (‖z.2‖-1),div_nonneg he hm.le]


/-- Local solutions have a uniform time on a fixed energy sublevel. -/
theorem Objective.uniform_local_energy_curve {m θ e : ℝ} {f : E→ℝ}
    (hf : Objective m f) (hθ : 0≤θ) (he : 0≤e) :
    ∃ a : ℝ,0<a ∧ ∀ z : E×E,energy f z.1 z.2≤e →
      ∃ γ : ℝ→E×E,γ 0=z ∧
        (∀ t∈Icc 0 a,HasDerivAt γ (vectorField θ f (γ t)) t) ∧
        ∀ t∈Icc 0 a,energy f (γ t).1 (γ t).2≤e := by
  obtain ⟨R,hR,hbound⟩ := hf.energy_sublevel_bounded he
  obtain ⟨K,hK⟩ := hf.vectorField_lipschitz_bounded (θ:=θ) (R+1)
  have hV0 : vectorField θ f (0:E×E)=0 := by simp [vectorField,hf.gradient_zero]
  let B : NNReal := ⟨R+1,by linarith⟩
  let r : NNReal := ⟨R,hR.le⟩
  let L : NNReal := K*B+1
  let a : ℝ := 1/(4*((L:ℝ)+1))
  have ha : 0<a := by dsimp [a]; positivity
  have hvbound (z : E×E) (hz : z∈closedBall 0 (B:ℝ)) : ‖vectorField θ f z‖≤L := by
    have hzero : (0:E×E)∈closedBall 0 (B:ℝ) := mem_closedBall_self B.coe_nonneg
    have hh := hK.norm_sub_le hz hzero
    rw [hV0,sub_zero,sub_zero] at hh
    have hz' := mem_closedBall_zero_iff.mp hz
    dsimp [L]
    exact hh.trans (by nlinarith [K.coe_nonneg])
  have htime : (L:ℝ)*max (2*a-0) (0-(-2*a))≤(B:ℝ)-(r:ℝ) := by
    have hp : 0<(L:ℝ)+1 := by positivity
    rw [sub_zero,show 0-(-2*a)=2*a by ring,max_self]
    change (L:ℝ)*(2*a)≤(R+1)-R
    dsimp [a]
    calc
      _ = ((L:ℝ)*2)/(4*((L:ℝ)+1)) := by ring
      _ ≤ 1 := (div_le_one (by positivity : 0<4*((L:ℝ)+1))).mpr
        (by nlinarith [L.coe_nonneg])
      _ = _ := by ring
  have hpl : IsPicardLindelof (fun _ => vectorField θ f)
      (tmin := -2*a) (tmax := 2*a) ⟨0,by constructor <;> linarith⟩
      (0:E×E) B r L K := IsPicardLindelof.of_time_independent hvbound hK htime
  refine ⟨a,ha,fun z hz => ?_⟩
  obtain ⟨γ,hγ0,hγd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (show z∈closedBall 0 (r:ℝ) from mem_closedBall_zero_iff.mpr (hbound z hz))
  change γ 0=z at hγ0
  have hd (t : ℝ) (ht : t∈Icc 0 a) : HasDerivAt γ (vectorField θ f (γ t)) t :=
    (hγd t ⟨by linarith [ht.1],by linarith [ht.2]⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
  have hp (t : ℝ) (ht : t∈Icc 0 a) : HasDerivAt (fun s => (γ s).1) (γ t).2 t := by
    simpa [Function.comp_def,vectorField] using
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hv (t : ℝ) (ht : t∈Icc 0 a) :
      HasDerivAt (fun s => (γ s).2) (-θ • (γ t).2-gradient f (γ t).1) t := by
    simpa [Function.comp_def,vectorField] using
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hd t ht)
  refine ⟨γ,hγ0,hd,fun t ht => ?_⟩
  have hh := energy_antitoneOn_Icc hf.differentiable hθ hp hv
    ⟨le_rfl,ha.le⟩ ht ht.1
  dsimp only at hh
  rw [hγ0] at hh
  exact hh.trans hz

/-- Global existence for all Hilbert initial positions and velocities. -/
theorem exists_solution {θ m : ℝ} {f : E→ℝ}
    (hθ : 0≤θ) (hf : Objective m f) (x₀ v₀ : E) :
    ∃ x v : ℝ→E,IsSolution θ f x v ∧ x 0=x₀ ∧ v 0=v₀ := by
  obtain ⟨a,ha,hloc⟩ := hf.uniform_local_energy_curve hθ (hf.energy_nonneg (x₀,v₀))
  obtain ⟨γ,hγ0,hγ⟩ := exists_forward_curve (V:=vectorField θ f)
    (S:={z:E×E | energy f z.1 z.2≤energy f x₀ v₀}) (x₀:=(x₀,v₀)) ha
    (show energy f x₀ v₀≤energy f x₀ v₀ from le_rfl) hloc
  refine ⟨fun t => (γ t).1,fun t => (γ t).2,⟨?_,?_⟩,?_,?_⟩
  · intro t ht
    simpa [Function.comp_def,vectorField] using
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t (hγ t ht).1
  · intro t ht
    simpa [Function.comp_def,vectorField] using
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hγ t ht).1
  · exact congrArg Prod.fst hγ0
  · exact congrArg Prod.snd hγ0

/-- Uniqueness uses a common bounded ball on each compact time interval. -/
theorem IsSolution.unique {θ m : ℝ} {f : E→ℝ} {x v y w : ℝ→E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hy : IsSolution θ f y w)
    (h₀ : x 0=y 0) (hv₀ : v 0=w 0) {t : ℝ} (ht : 0≤t) : x t=y t ∧ v t=w t := by
  let α := fun s => (x s,v s)
  let β := fun s => (y s,w s)
  have hdα (s : ℝ) (hs : 0≤s) : HasDerivAt α (vectorField θ f (α s)) s :=
    (hx.position_derivative s hs).prodMk (hx.velocity_derivative s hs)
  have hdβ (s : ℝ) (hs : 0≤s) : HasDerivAt β (vectorField θ f (β s)) s :=
    (hy.position_derivative s hs).prodMk (hy.velocity_derivative s hs)
  have hcα : ContinuousOn α (Icc 0 t) := fun s hs => (hdα s hs.1).continuousAt.continuousWithinAt
  have hcβ : ContinuousOn β (Icc 0 t) := fun s hs => (hdβ s hs.1).continuousAt.continuousWithinAt
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:E×E)).mp
    (((isCompact_Icc.image_of_continuousOn hcα).union
      (isCompact_Icc.image_of_continuousOn hcβ)).isBounded)
  obtain ⟨K,hK⟩ := hf.vectorField_lipschitz_bounded (θ:=θ) R
  have heq := ODE_solution_unique_of_mem_Icc_right (v:=fun _ => vectorField θ f)
    (s:=fun _ => closedBall (0:E×E) R) (fun _ _ => hK) hcα
    (fun s hs => (hdα s hs.1).hasDerivWithinAt)
    (fun s hs => hR (Or.inl ⟨s,⟨hs.1,hs.2.le⟩,rfl⟩)) hcβ
    (fun s hs => (hdβ s hs.1).hasDerivWithinAt)
    (fun s hs => hR (Or.inr ⟨s,⟨hs.1,hs.2.le⟩,rfl⟩))
    (show α 0=β 0 from Prod.ext h₀ hv₀) ⟨ht,le_rfl⟩
  exact ⟨congrArg Prod.fst heq,congrArg Prod.snd heq⟩

/-- Existence and uniqueness for the literal half-line heavy-ball equation. -/
theorem exists_unique_solution {θ m : ℝ} {f : E→ℝ}
    (hθ : 0<θ) (hf : Objective m f) (x₀ v₀ : E) :
    ∃ x v : ℝ→E,IsSolution θ f x v ∧ x 0=x₀ ∧ v 0=v₀ ∧
      ∀ y w,IsSolution θ f y w → y 0=x₀ → w 0=v₀ →
        ∀ t,0≤t → y t=x t ∧ w t=v t := by
  obtain ⟨x,v,hx,hx₀,hv₀⟩ := exists_solution hθ.le hf x₀ v₀
  exact ⟨x,v,hx,hx₀,hv₀,fun y w hy hy₀ hw₀ t ht =>
    hy.unique hf hx (hy₀.trans hx₀.symm) (hw₀.trans hv₀.symm) ht⟩

end
end nesterov.Flow
