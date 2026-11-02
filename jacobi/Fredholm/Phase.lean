import jacobi.Fredholm.TurningRatio
import jacobi.Young.SemilinearUniqueness

/-!
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
The exact first integral has a C1 positive-part polynomial derivative and
one simple upper turning zero. Its associated clipped polynomial vector
field is locally Lipschitz on the entire plane. This supplies true uniqueness
through both the switching level and the central turning point.
Source: exact rational turning monotonicity and the reused Picard--Lindelof continuation theorem.
Use: reflection and profile uniqueness use a genuine globally locally Lipschitz field, with no division by g.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set Filter jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual polynomial clipped acceleration obtained from the zero Green first integral.
Use: reflection and profile uniqueness use a genuine globally locally Lipschitz field, with no division by g.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
-/
def force (A e g : ℝ) : ℝ := 4*g-2-(2/3:ℝ)*A^2*(max (g-e) 0)^3-2*A^2*g*(max (g-e) 0)^2

/-- The actual Fredholm phase has its exact derivative at every real point, including the switching level.
Use: determines the strict acceleration sign at the unique upper turning zero.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: the positive cube is C1 across the cutoff. Differentiate its product
with gamma and the original quadratic free term, then simplify the exact polynomial. -/
theorem phase_hasDerivAt (A e g : ℝ) : HasDerivAt (phase A e) (2*force A e g) g := by
  -- The positive cube is differentiable even at the clipping boundary.
  have hp := (positiveCube_hasDerivAt (g-e)).comp g ((hasDerivAt_id g).sub_const e)
  convert ((((hasDerivAt_id g).const_mul 2).sub_const 1).pow 2).sub
    (((hasDerivAt_id g).mul hp).const_mul ((4/3:ℝ)*A^2)) using 1
  · funext t
    dsimp only [phase,Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,Function.comp_def,id_eq]
    ring
  · unfold force
    dsimp only [Pi.mul_apply,Function.comp_def,id_eq]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring

/-- Above the switching level the literal phase has the exact monotone-ratio factorization.
Use: the proved ratio root determines the full phase sign pattern.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: use the actual positive branch and clear the nonzero quadratic denominator. -/
theorem phase_factor {A e g : ℝ} (he : (1/2:ℝ)≤e) (hg : e<g) :
    phase A e g=(2*g-1)^2*(1-(4/3:ℝ)*A^2*turningRatio e g) := by
  have hd : 2*g-1≠0 := by linarith
  unfold phase turningRatio
  rw [max_eq_left (sub_pos.mpr hg).le]
  field_simp

/-- The actual Fredholm phase has one unique upper zero, its full sign pattern and a strictly negative derivative there.
Use: fixes the true peak and excludes every secondary critical point of an actual optimizing Green profile.
Article: jacobi, Theorem D.7.
Proof: the actual ratio has one positive target root. Its strict monotonicity
fixes both phase signs above the cutoff; below the cutoff the phase is the
free positive square. Differentiating the same local factorization gives
strictly negative derivative at the upper root. -/
theorem phase_turning {A e : ℝ} (hA : 0<A) (he : (1/2:ℝ)≤e) :
    ∃ g0 : ℝ,e<g0 ∧ phase A e g0=0 ∧
      (∀ g : ℝ,(1/2:ℝ)<g → g<g0 → 0<phase A e g) ∧
      (∀ g : ℝ,g0<g → phase A e g<0) ∧ force A e g0<0 := by
  -- Construct the turning level from the actual original rational ratio.
  obtain ⟨g0,hg0,hroot,_huniq⟩ := turningRatio_root hA he
  have hcoef : 0<(4/3:ℝ)*A^2 := by positivity
  have hone : (4/3:ℝ)*A^2*turningRatio e g0=1 := by rw [hroot]; field_simp
  have hz : phase A e g0=0 := by rw [phase_factor he hg0,hone,sub_self,mul_zero]
  have hbelow (g : ℝ) (hg : (1/2:ℝ)<g) (hgg : g<g0) : 0<phase A e g := by
    by_cases hge : e<g
    · have hh := (turningRatio_strictMono he) hge.le hg0.le hgg
      have hlt := mul_lt_mul_of_pos_left hh hcoef
      rw [hone] at hlt
      rw [phase_factor he hge]
      exact mul_pos (sq_pos_of_pos (by linarith)) (sub_pos.mpr hlt)
    · unfold phase
      rw [max_eq_right (by linarith : g-e≤0),zero_pow (by decide : 3≠0),mul_zero,sub_zero]
      exact sq_pos_of_pos (by linarith)
  have habove (g : ℝ) (hg : g0<g) : phase A e g<0 := by
    have hh := (turningRatio_strictMono he) hg0.le (hg0.trans hg).le hg
    have hlt := mul_lt_mul_of_pos_left hh hcoef
    rw [hone] at hlt
    rw [phase_factor he (hg0.trans hg)]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (by linarith)) (sub_neg.mpr hlt)
  have hR := turningRatio_hasDerivAt e (he.trans_lt hg0)
  have hRd := turningRatio_derivative_pos he hg0
  have hfactor : phase A e=ᶠ[𝓝 g0] fun g => (2*g-1)^2*(1-(4/3:ℝ)*A^2*turningRatio e g) := by
    filter_upwards [Ioi_mem_nhds hg0] with g hg
    exact phase_factor he hg
  have hF := (((((hasDerivAt_id g0).const_mul 2).sub_const 1).pow 2).mul
    ((hR.const_mul ((4/3:ℝ)*A^2)).const_sub 1)).congr_of_eventuallyEq hfactor
  have hid := (phase_hasDerivAt A e g0).unique hF
  rw [hone] at hid
  norm_num only [sub_self,mul_zero,zero_sub,Nat.cast_ofNat,Nat.reduceSub,pow_one,id_eq,Pi.pow_apply] at hid
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos (show 0<2*g0-1 by linarith))
    (neg_neg_of_pos (mul_pos hcoef hRd))
  exact ⟨g0,hg0,hz,hbelow,habove,by nlinarith⟩

/-- The actual autonomous Fredholm profile field on the full value/slope plane.
Use: global uniqueness and reflection remain valid across the free boundary.
Article: jacobi, Theorem D.7.
-/
def profileField (A e : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.2,force A e z.1)

/-- The true clipped Fredholm profile field is locally Lipschitz everywhere.
Use: discharges Picard--Lindelof regularity rather than assuming uniqueness of candidate profiles.
Article: jacobi, Theorem D.7.
Proof: compose the globally Lipschitz positive-part embedding with a smooth polynomial map of the enlarged coordinates. -/
theorem profileField_locallyLipschitz (A e : ℝ) : LocallyLipschitz (profileField A e) := by
  let H (z : (ℝ × ℝ) × ℝ) : ℝ × ℝ := (z.1.2,4*z.1.1-2-(2/3:ℝ)*A^2*z.2^3-2*A^2*z.1.1*z.2^2)
  have hH : ContDiff ℝ 1 H := by unfold H; fun_prop
  have hsub : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1-e) := by fun_prop
  have hmax : LocallyLipschitz (fun z : ℝ × ℝ => max (z.1-e) 0) :=
    (LipschitzWith.id.max_const 0).locallyLipschitz.comp hsub.locallyLipschitz
  have hE : LocallyLipschitz (fun z : ℝ × ℝ => (z,max (z.1-e) 0)) :=
    LipschitzWith.id.locallyLipschitz.prodMk hmax
  exact hH.locallyLipschitz.comp hE

/-- Equal value and slope at one point identify entire actual Fredholm profile trajectories.
Use: reflection at turning points and exclusion of repeated turning points.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Source: Picard--Lindelof uniqueness and connected continuation, reused from jacobi.
Proof: apply the verified autonomous planar uniqueness theorem to the actual locally Lipschitz clipped Fredholm field. -/
theorem profile_unique {f d g k : ℝ → ℝ} (A e b : ℝ)
    (hf : ∀ x,HasDerivAt f (d x) x) (hd : ∀ x,HasDerivAt d (force A e (f x)) x)
    (hg : ∀ x,HasDerivAt g (k x) x) (hk : ∀ x,HasDerivAt k (force A e (g x)) x)
    (h0 : f b=g b) (h1 : d b=k b) : f=g ∧ d=k := by
  have hh := jacobi.Young.autonomous_unique (profileField_locallyLipschitz A e)
    (fun x => (hf x).prodMk (hd x)) (fun x => (hg x).prodMk (hk x)) (Prod.ext h0 h1)
  exact ⟨funext fun x => congrArg Prod.fst (congrFun hh x),funext fun x => congrArg Prod.snd (congrFun hh x)⟩

end
end jacobi.Fredholm
