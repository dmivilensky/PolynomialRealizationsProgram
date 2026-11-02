import krylov.OneGradient.KnownBaseCentreGeometry
import krylov.OneGradient.Information
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), original arbitrary-method reference length.
Use: tie a finite four-adversary lower bound to the true penultimate
reference energy error for every actual span-restricted M1 policy.
Source: genuine observed Krylov containment, actual complete CG frame,
the exact canonical gradient update and real inner-product norm bounds.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace

/-- Every actual first M1 query is a scalar multiple of its observed
initial gradient, with no consistency, continuity or nonzero premise.
Use: the original known-base reference's last normal annihilates the
first query of every competing method.
Article: main_krylov, thm:local(c), genuine first-query information.
Proof: true observed Krylov containment at index zero is the span of the
single zeroth operator power; singleton-span membership gives the scalar. -/
theorem oneGradient_first_query_scalar
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m) (Q : E →L[ℝ] E) (g : E) :
    ∃ a : ℝ,oneGradientStep m (fun _ => Q) g 0=a • g := by
  have hs := one_gradient_step_krylov m hm Q g 0
  have hset : ((fun i : ℕ => (Q^i) g) '' Set.Iio 1)={g} := by
    ext v
    simp only [Set.mem_image,Set.mem_Iio,Nat.lt_one_iff,pow_zero,one_apply_eq_self,
      Set.mem_singleton_iff,exists_eq_left]
    exact eq_comm
  rw [krylov_space_powers,hset] at hs
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hs
  exact ⟨a,ha.symm⟩

/-- The actual full-atom reference error is bounded by the real second
query length plus the actual unperturbed incoming-gradient mismatch, for
every genuine span-restricted M1 method. Degenerate queries are included.
Use: original minimax normalization follows from actual CG geometry;
no CG consistency or order estimate for a competing method is assumed.
Article: main_krylov, thm:local(c), true reference-length triangle bound.
Proof: the genuine last CG normal annihilates the first CG step and hence
the entire one-dimensional first information span. The exact last-gradient
and first-update identities give its true initial normal component. Pair
the actual reference residual with that unit normal and apply Cauchy. -/
theorem twoQuery_reference_length_bound
    (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin 2))) (hm : OneGradientSpanRestricted m) :
    let Q := cgOperator base
    let R := cgOperator (metricRoot base)
    let b := cgOperator (metricRoot base)⁻¹ g
    let v0 := R (oneGradientStep m (fun _ => Q) g 0)
    let v := R (oneGradientStep m (fun _ => Q) g 1)
    ‖cgCanonicalError base g 1‖≤‖v‖+‖b+v0+v‖ := by
  let Q := cgOperator base
  let R := cgOperator (metricRoot base)
  let b := cgOperator (metricRoot base)⁻¹ g
  let h := canonicalCGUnitStep base g 1
  let sigma := ‖canonicalCGStep base g 1‖
  let v0 := R (oneGradientStep m (fun _ => Q) g 0)
  let v := R (oneGradientStep m (fun _ => Q) g 1)
  let r := b+v0+v
  have hplane := knownBaseCentre_reference_plane base hb g hc
  have hh : ‖h‖=1 := hplane.2.1
  have horth : inner ℝ h (canonicalCGUnitStep base g 0)=0 := by rw [real_inner_comm];exact hplane.2.2.1
  have hstep : inner ℝ h (canonicalCGStep base g 0)=0 := by
    have hs := NormedSpace.norm_smul_normalize (canonicalCGStep base g 0)
    change ‖canonicalCGStep base g 0‖ • canonicalCGUnitStep base g 0=canonicalCGStep base g 0 at hs
    rw [← hs,real_inner_smul_right,horth,mul_zero]
  have halpha : cgLine base g 0≠0 := (cgLength_pos base hb g 0 (by rw [hc];decide)).ne'
  have hRg : inner ℝ h (R g)=0 := by
    have hs : canonicalCGStep base g 0= -(cgLine base g 0) • R g := by
      simp only [canonicalCGStep,cgStep,cgRun,map_smul,map_neg,smul_neg,neg_smul,R]
      rfl
    rw [hs,real_inner_smul_right] at hstep
    exact (mul_eq_zero.mp hstep).resolve_left (neg_ne_zero.mpr halpha)
  obtain ⟨a,ha⟩ := oneGradient_first_query_scalar m hm Q g
  have hv0 : inner ℝ h v0=0 := by
    change inner ℝ h (R (oneGradientStep m (fun _ => Q) g 0))=0
    rw [ha,map_smul,real_inner_smul_right,hRg,mul_zero]
  have hlast := canonicalCG_last_gradient base hb g (canonicalCG_frame_of_full_atoms base hb g hc)
  have hupdate := canonicalCG_gradient_step base hb g 0
  have hnormal : inner ℝ h b= -sigma := by
    have he : cgOperator (metricRoot base)⁻¹ (CG.gradient Q g 1)=b+canonicalCGStep base g 0 := hupdate
    have hl : cgOperator (metricRoot base)⁻¹ (CG.gradient Q g 1)= -sigma • h := hlast
    have hi := congrArg (fun x => inner ℝ h x) (he.symm.trans hl)
    rw [inner_add_right,hstep,add_zero,real_inner_smul_right,real_inner_self_eq_norm_sq,hh,one_pow,mul_one] at hi
    exact hi
  have hr : inner ℝ h r= -sigma+inner ℝ h v := by
    dsimp only [r]
    rw [inner_add_right,inner_add_right,hnormal,hv0,add_zero]
  have hvbound : |inner ℝ h v|≤‖v‖ := by simpa only [hh,one_mul] using abs_real_inner_le_norm h v
  have hrbound : |inner ℝ h r|≤‖r‖ := by simpa only [hh,one_mul] using abs_real_inner_le_norm h r
  have hbound : sigma≤‖v‖+‖r‖ := by
    linarith [le_abs_self (inner ℝ h v),neg_le_abs (inner ℝ h r)]
  dsimp only
  rw [(knownBaseCentre_reference_scale base hb g hc).2]
  exact hbound

end
end krylov.OneGradient
