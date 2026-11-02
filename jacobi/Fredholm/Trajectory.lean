import jacobi.Fredholm.Phase
import jacobi.Elliptic.PhaseGeometry

/-!
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
The actual clipped autonomous equation is symmetric at a turning point.
A second turning point would repeat the entire trajectory with a positive
period, contradicting its strict peak above the free limit. The proved
negative turning acceleration selects the descending branch globally.
Source: the proved Fredholm profile uniqueness and the reused periodic-limit theorem.
Use: centers the true optimizer and supplies reflection of its spatial quadratures.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every actual Fredholm trajectory is symmetric about each of its zero-slope points.
Use: centers the true optimizer and supplies reflection of its spatial quadratures.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: reflect the value and negate the reflected slope. They solve the
same proved locally Lipschitz autonomous field with the same actual initial data. -/
theorem profile_reflect {f d : ℝ → ℝ} (A e b : ℝ)
    (hf : ∀ x,HasDerivAt f (d x) x) (hd : ∀ x,HasDerivAt d (force A e (f x)) x) (hdb : d b=0) :
    (∀ x,f (2*b-x)=f x) ∧ (∀ x,d (2*b-x)=-d x) := by
  -- The reflected slope sign is essential to the actual second-order equation.
  have hg (x : ℝ) : HasDerivAt (fun y => f (2*b-y)) (-d (2*b-x)) x := by
    simpa only [Function.comp_def,mul_neg_one] using
      (hf (2*b-x)).comp x ((hasDerivAt_id x).const_sub (2*b))
  have hk (x : ℝ) : HasDerivAt (fun y => -d (2*b-y)) (force A e (f (2*b-x))) x := by
    convert ((hd (2*b-x)).comp x ((hasDerivAt_id x).const_sub (2*b))).neg using 1
    · rfl
    · ring
  have hu := profile_unique A e b hf hd hg hk (by rw [show 2*b-b=b by ring])
    (by rw [show 2*b-b=b by ring,hdb,neg_zero])
  refine ⟨fun x => (congrFun hu.1 x).symm,fun x => ?_⟩
  have h := congrFun hu.2 x
  change d x=-d (2*b-x) at h
  linarith

/-- A true decaying Fredholm trajectory has no second critical point after its upper turn.
Use: fixes one genuine square-root Jacobian on the whole positive half-line.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: the exact phase sign pattern forces a second critical state to have
the same turning value. Actual autonomous uniqueness then gives a positive
period; the proved periodic-limit theorem contradicts the strict upper peak. -/
theorem no_second_turning {f d : ℝ → ℝ} {A e b : ℝ}
    (hf : ∀ x,HasDerivAt f (d x) x) (hd : ∀ x,HasDerivAt d (force A e (f x)) x)
    (hfirst : ∀ x,d x^2=phase A e (f x)) (hdb : d b=0)
    (hlower : ∀ x,(1/2:ℝ)<f x) (hlim : Tendsto f atTop (𝓝 (1/2:ℝ)))
    (hbelow : ∀ g : ℝ,(1/2:ℝ)<g → g<f b → 0<phase A e g)
    (habove : ∀ g : ℝ,f b<g → phase A e g<0) {x : ℝ} (hx : b<x) : d x≠0 := by
  -- A repeated critical state repeats the actual entire solution, not just the scalar energy level.
  intro hdx
  have hfx : f x=f b := by
    rcases lt_trichotomy (f x) (f b) with hlt | heq | hgt
    · have hh := hfirst x
      have hp := hbelow _ (hlower x) hlt
      rw [hdx] at hh
      nlinarith
    · exact heq
    · have hh := hfirst x
      have hn := habove _ hgt
      rw [hdx] at hh
      nlinarith
  let p := x-b
  have hp : 0<p := sub_pos.mpr hx
  have hg (z : ℝ) : HasDerivAt (fun y => f (y+p)) (d (z+p)) z := by
    simpa only [Function.comp_def,id_eq,mul_one] using (hf (z+p)).comp z ((hasDerivAt_id z).add_const p)
  have hk (z : ℝ) : HasDerivAt (fun y => d (y+p)) (force A e (f (z+p))) z := by
    simpa only [Function.comp_def,id_eq,mul_one] using (hd (z+p)).comp z ((hasDerivAt_id z).add_const p)
  have hb : b+p=x := by unfold p; ring
  have hu := profile_unique A e b hf hd hg hk (by rw [hb,hfx]) (by rw [hb,hdb,hdx])
  have hper : Function.Periodic f p := fun z => (congrFun hu.1 z).symm
  have hz := jacobi.Elliptic.periodic_eq_limit hp hper hlim b
  exact (hlower b).ne' hz

/-- The genuine descending Fredholm profile has strictly negative slope everywhere after its upper turn.
Use: the spatial Jacobian uses the negative square root of the true phase.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: the proved strictly negative upper-turn acceleration gives a short
interval of negative slope. Any later nonnegative slope would cross zero,
contradicting the proved absence of a second turning point. -/
theorem descending_slope {f d : ℝ → ℝ} {A e b : ℝ}
    (hf : ∀ x,HasDerivAt f (d x) x) (hd : ∀ x,HasDerivAt d (force A e (f x)) x)
    (hfirst : ∀ x,d x^2=phase A e (f x)) (hdb : d b=0)
    (hlower : ∀ x,(1/2:ℝ)<f x) (hlim : Tendsto f atTop (𝓝 (1/2:ℝ)))
    (hbelow : ∀ g : ℝ,(1/2:ℝ)<g → g<f b → 0<phase A e g)
    (habove : ∀ g : ℝ,f b<g → phase A e g<0) (hforce : force A e (f b)<0)
    {x : ℝ} (hx : b<x) : d x<0 := by
  -- The actual initial slope and acceleration determine the globally consistent branch.
  have hD : HasDerivAt (fun t : ℝ => d (b+t)) (force A e (f b)) 0 := by
    simpa only [Function.comp_def,id_eq,add_zero,mul_one] using
      (hd (b+id 0)).comp 0 ((hasDerivAt_id (0:ℝ)).const_add b)
  have he := jacobi.Variational.HasDerivAt.eventually_right_descent hD hforce
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,t<x-b := by
    have hh : ∀ᶠ t : ℝ in 𝓝 0,t<x-b := Iio_mem_nhds (sub_pos.mpr hx)
    exact hh.filter_mono nhdsWithin_le_nhds
  obtain ⟨t,htd,htx,htp⟩ := (he.and (hsmall.and self_mem_nhdsWithin)).exists
  have ht0 : 0<t := htp
  have hneg : d (b+t)<0 := by simpa only [add_zero,hdb] using htd
  by_contra! hdx
  have hc : Continuous d := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  obtain ⟨z,hz,hdz⟩ := (intermediate_value_Icc (show b+t≤x by linarith) hc.continuousOn) ⟨hneg.le,hdx⟩
  exact no_second_turning hf hd hfirst hdb hlower hlim hbelow habove
    (by have hh := hz.1; linarith : b<z) hdz

end
end jacobi.Fredholm
