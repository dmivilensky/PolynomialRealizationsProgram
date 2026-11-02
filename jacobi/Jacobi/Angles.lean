import jacobi.Jacobi.OrderedReflection
import jacobi.Jacobi.OrderedZeroLimit
import jacobi.Bessel.EdgeSequence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
Article: jacobi, Proposition B.1.
The actual ordered Jacobi nodes have their canonical angles in (0,pi),
with complete ordered reflection. Fixed-index angular zeros have the full
Mehler--Heine limit n*theta_(n,k) -> j_(alpha,k).
Use: all angular estimates refer to the original polynomial zero enumeration.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The canonical angle of an actual finite Jacobi zero.
Use: all angular estimates refer to the original polynomial zero enumeration.
Article: jacobi, Proposition B.1.
-/
def angle (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) : ℝ :=
  arccos ((nodes a b ha hb n).value i)

/-- Each genuine angular Jacobi zero lies strictly between zero and pi and has the prescribed original node as its cosine.
Use: identifies the angular list used in all Liouville and both-edge comparisons.
Article: jacobi, Proposition B.1.
Proof: apply the community inverse-cosine branch theorem to the already proved actual node interval. -/
theorem angle_properties {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) :
    angle a b ha hb i∈Ioo 0 Real.pi ∧ cos (angle a b ha hb i)=(nodes a b ha hb n).value i := by
  obtain ⟨hlo,hhi⟩ := (nodes a b ha hb n).interval i
  exact ⟨⟨arccos_pos.mpr hhi,arccos_lt_pi.mpr hlo⟩,cos_arccos hlo.le hhi.le⟩

/-- The complete actual Jacobi angular zero list is strictly increasing.
Use: fixes the source numbering for the full both-edge zero theorem.
Article: jacobi, Proposition B.1.
Proof: the actual nodes strictly decrease and inverse cosine strictly decreases on their genuine interval. -/
theorem angle_strictMono {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    StrictMono (fun i : Fin n => angle a b ha hb i) := by
  intro i j hij
  exact arccos_lt_arccos ((nodes a b ha hb n).interval j).1.le
    ((nodes a b ha hb n).strictAnti hij) ((nodes a b ha hb n).interval i).2.le

/-- The actual canonical angular zero lists reflect exactly in reverse finite order.
Use: reduces the opposite-edge angular estimates to the parameter-exchanged original family.
Article: jacobi, Proposition B.1.
Proof: use the proved ordered node reflection and the community inverse-cosine reflection identity. -/
theorem angle_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) :
    angle a b ha hb i.rev=Real.pi-angle b a hb ha i := by
  rw [angle,nodes_reflection ha hb i,arccos_neg,angle]

/-- The actual finite angle list padded by zero after the degree, expressed directly through the proved squared spectral zeros.
Use: gives a common natural index for angular Mehler--Heine convergence, including degree zero.
Article: jacobi, Proposition B.1.
-/
def finiteAngleAt (a b : ℝ) (ha : -1<a) (hb : -1<b) (n k : ℕ) : ℝ :=
  arccos (1-finiteSigmaAt a b ha hb n k/(2*(n:ℝ)^2))

/-- Every valid padded angular entry is precisely the angle of the original actual Jacobi node.
Use: no artificial angular zero sequence replaces the one in the source.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: substitute the actual finite squared-zero formula and cancel the positive degree-squared scale. -/
theorem finiteAngleAt_eq {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    finiteAngleAt a b ha hb n k=angle a b ha hb ⟨k,hk⟩ := by
  unfold finiteAngleAt angle
  rw [finiteSigmaAt_eq ha hb hk,finiteSigma_node ha hb ⟨k,hk⟩]
  have hn : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  congr 1
  field_simp [hn]
  ring

/-- Each actual fixed-index Jacobi angle tends to zero.
Use: allows the continuous sinc normalization to convert the actual squared-zero limit to the full angular limit.
Article: jacobi, Proposition B.1.
Proof: the genuine squared zeros converge to their finite positive Bessel
limits while inverse degree squared tends to zero; continuity of inverse
cosine at one fixes the actual principal angle limit. -/
theorem finiteAngleAt_tendsto_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) (k : ℕ) :
    Tendsto (fun n : ℕ => finiteAngleAt a b ha hb n k) atTop (𝓝 0) := by
  -- This uses the full canonically indexed squared-zero limit already proved for the actual finite list.
  have hi : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hp := (finiteSigmaAt_tendsto ha hb k).mul ((hi.pow 2).div_const 2)
  simp only [zero_pow (by norm_num : 2≠0),zero_div,mul_zero] at hp
  have he : (fun n : ℕ => finiteSigmaAt a b ha hb n k*((1/(n:ℝ))^2/2))=
      fun n : ℕ => finiteSigmaAt a b ha hb n k/(2*(n:ℝ)^2) := by
    funext n
    ring
  rw [he] at hp
  have h := Real.continuous_arccos.continuousAt.tendsto.comp ((tendsto_const_nhds (x := (1:ℝ))).sub hp)
  simpa only [finiteAngleAt,sub_zero,arccos_one,Function.comp_def] using h

/-- The square root of every genuine finite squared spectral zero is exactly its positive half-angle sine scaling.
Use: converts the proved squared-zero convergence to the actual fixed-index angular Mehler--Heine limit.
Article: jacobi, Proposition B.1.
Proof: use the actual cosine node identity and the community half-angle
square-root formula on its genuine positive branch; the natural degree
has nonnegative scale, so its square root is unambiguous. -/
theorem angle_spectral_sqrt {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (i : Fin n) :
    √(finiteSigma a b ha hb n i)=2*(n:ℝ)*sin (angle a b ha hb i/2) := by
  -- The positive half-angle branch follows from the true original node interval.
  have ht := (angle_properties ha hb i).1
  rw [finiteSigma_node ha hb i,← (angle_properties ha hb i).2,
    show 2*(n:ℝ)^2*(1-cos (angle a b ha hb i))=
      (2*(n:ℝ))^2*((1-cos (angle a b ha hb i))/2) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0≤2*(n:ℝ)),
    ← Real.sin_half_eq_sqrt ht.1.le (by linarith [ht.2,Real.pi_pos])]

/-- The full actual angular Mehler--Heine zero limit holds for every fixed canonical source index.
Use: supplies the fixed small-index angular estimates and gap limits in the uniform both-edge proof.
Article: jacobi, Proposition B.1.
Proof: the genuine angle tends to zero and its sinc normalization tends
to one. The exact positive half-angle identity expresses n times that
angle as the square root of the genuine squared zero divided by sinc.
The already proved canonically indexed squared-zero limit finishes the argument. -/
theorem finiteAngleAt_scaled_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)*finiteAngleAt a b ha hb n k) atTop
      (𝓝 (jacobi.Bessel.positiveZero a ha k)) := by
  -- Continuity of sinc at zero avoids any unsupported cancellation in a punctured limiting formula.
  have hangle := (finiteAngleAt_tendsto_zero ha hb k).div_const 2
  simp only [zero_div] at hangle
  have hsinc := Real.continuous_sinc.continuousAt.tendsto.comp hangle
  simp only [Real.sinc_zero,Function.comp_def] at hsinc
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp (finiteSigmaAt_tendsto ha hb k)
  have h := hroot.div hsinc (by norm_num : (1:ℝ)≠0)
  simp only [div_one] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop k] with n hn
  change (n:ℝ)*finiteAngleAt a b ha hb n k=
    √(finiteSigmaAt a b ha hb n k)/sinc (finiteAngleAt a b ha hb n k/2)
  rw [finiteAngleAt_eq ha hb hn,finiteSigmaAt_eq ha hb hn,angle_spectral_sqrt ha hb ⟨k,hn⟩]
  have ht := (angle_properties ha hb (⟨k,hn⟩:Fin n)).1
  have hhalf : 0<angle a b ha hb (⟨k,hn⟩:Fin n)/2 := by linarith [ht.1]
  have hsin := Real.sin_pos_of_pos_of_lt_pi hhalf (by linarith [ht.2,Real.pi_pos])
  rw [Real.sinc_of_ne_zero hhalf.ne']
  field_simp [hsin.ne']

end
end jacobi.Jacobi
