import polyak.General.IQC.BoundedLoop

/-!
Article: Lemma `homotopy` with its original nonlinear-operator assumptions.
Only causality and the gain bound from zero are required. No continuity or
incremental Lipschitz bound is imposed on the nonlinear operator. The existing
finite continuation and quadratic a priori proofs are instantiated literally.
-/
namespace nesterov.IQC
noncomputable section
open Set polyak.General.IQC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure CausalFeedback (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  plant : (ℕ → E) →ₗ[ℝ] (ℕ → E)
  strictlyCausal : StrictCausal plant
  gain : ℝ
  gain_nonneg : 0≤gain
  prefix_gain : ∀ x N,prefixNorm (plant x) N≤gain*prefixNorm x N
  delta : (ℕ → E) → ℕ → E
  delta_causal : Causal delta
  delta_prefix_bound : ∀ x N,prefixNorm (delta x) N≤prefixNorm x N

namespace CausalFeedback
variable (F : CausalFeedback E)

def loop (τ : ℝ) (x : ℕ → E) : ℕ → E := F.plant (τ • F.delta x)

theorem loop_strictCausal (τ : ℝ) : StrictCausal (F.loop τ) := by
  intro k x y hxy
  apply F.strictlyCausal
  intro j hj
  exact congrArg (fun z : E => τ • z) (F.delta_causal k x y hxy j hj)

def run (τ : ℝ) (f : ℕ → E) : ℕ → E := causalSolve (F.loop τ) f

theorem run_equation (τ : ℝ) (f : ℕ → E) :
    F.run τ f=F.plant (τ • F.delta (F.run τ f))+f := by
  funext n
  exact causalSolve_equation (F.loop_strictCausal τ) f n

theorem run_causal (τ : ℝ) : Causal (F.run τ) :=
  causalSolve_causal (F.loop_strictCausal τ)

/-- Every unrestricted solution is the actual causal execution. -/
theorem eq_run_of_equation (τ : ℝ) (f x : ℕ→E)
    (hx : x=F.plant (τ • F.delta x)+f) : x=F.run τ f := by
  apply causalSolve_unique (F.loop_strictCausal τ) f x
  intro k
  exact congrFun hx k

/-- Strict causality gives existence and uniqueness before any summability
or continuity of the nonlinear operator is known. -/
theorem existsUnique_solution (τ : ℝ) (f : ℕ→E) :
    ∃! x : ℕ→E,x=F.plant (τ • F.delta x)+f := by
  refine ⟨F.run τ f,F.run_equation τ f,?_⟩
  intro x hx
  exact F.eq_run_of_equation τ f x hx

def Stable (τ : ℝ) : Prop := ∀ f : ℕ → E,SquareSummable f → SquareSummable (F.run τ f)

def Apriori (C : ℝ) (τ : ℝ) : Prop :=
  ∀ f : ℕ → E,SquareSummable f → SquareSummable (F.run τ f) →
    sequenceNorm (F.run τ f)≤C*sequenceNorm f

theorem stable_zero : F.Stable 0 := by
  intro f hf
  have he : F.run 0 f=f := by
    rw [F.run_equation]
    simp only [zero_smul,map_zero,zero_add]
  rwa [he]

/-- The small-step proof uses only a finite forcing prefix, hence does not
assume that the target solution or its nonlinear response is in ℓ². -/
theorem stable_step {C τ τ' : ℝ} (hC : 0<C) (hs : F.Stable τ)
    (ha : F.Apriori C τ) (hstep : C*F.gain*|τ'-τ|≤1/2) : F.Stable τ' := by
  intro f hf
  let x:=F.run τ' f
  let g:=f+F.plant ((τ'-τ) • F.delta x)
  have hx : x=F.run τ g := by
    apply causalSolve_unique (F.loop_strictCausal τ) g x
    intro k
    have he:=congrFun (F.run_equation τ' f) k
    change x k=F.plant (τ • F.delta x) k+g k
    have hlin : F.plant (τ' • F.delta x)=
        F.plant (τ • F.delta x)+F.plant ((τ'-τ) • F.delta x) := by
      rw [←map_add,←add_smul]
      rw [show τ+(τ'-τ)=τ' by ring]
    change x k=F.plant (τ' • F.delta x) k+f k at he
    rw [hlin] at he
    simpa only [g,Pi.add_apply,add_comm,add_left_comm,add_assoc] using he
  have hprefix (N : ℕ) : prefixNorm x N≤2*C*sequenceNorm f := by
    let gN:=truncate N g
    have hgN : SquareSummable gN:=squareSummable_truncate g N
    have hy : SquareSummable (F.run τ gN):=hs gN hgN
    have heq : prefixNorm x N=prefixNorm (F.run τ gN) N := by
      rw [hx]
      exact prefixNorm_congr (F.run_causal τ N g gN (fun _ hk => (ite_eq_left hk).symm))
    have hpre : prefixNorm x N≤C*prefixNorm g N := by
      rw [heq]
      exact (prefixNorm_le_sequenceNorm hy N).trans
        ((ha gN hgN hy).trans_eq (by rw [sequenceNorm_truncate]))
    have hg : prefixNorm g N≤sequenceNorm f+F.gain*|τ'-τ| * prefixNorm x N := by
      calc
        _≤prefixNorm f N+prefixNorm (F.plant ((τ'-τ) • F.delta x)) N :=
          prefixNorm_triangle _ _ N
        _≤sequenceNorm f+F.gain*prefixNorm ((τ'-τ) • F.delta x) N :=
          add_le_add (prefixNorm_le_sequenceNorm hf N) (F.prefix_gain _ N)
        _=sequenceNorm f+F.gain*(|τ'-τ| * prefixNorm (F.delta x) N) := by rw [prefixNorm_smul]
        _≤sequenceNorm f+F.gain*(|τ'-τ| * prefixNorm x N) := by
          have hm:=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (F.delta_prefix_bound x N) (abs_nonneg (τ'-τ)))
            F.gain_nonneg
          linarith
        _=_ := by ring
    have hh:=hpre.trans (mul_le_mul_of_nonneg_left hg hC.le)
    have hsmall:=mul_le_mul_of_nonneg_right hstep (prefixNorm_nonneg x N)
    nlinarith
  exact squareSummable_of_prefix_bound hprefix

/-- Finitely many uniformly sized continuation steps reach every τ∈[0,1]. -/
theorem stable_of_apriori {C : ℝ} (hC : 0<C)
    (ha : ∀ τ : ℝ,τ∈Icc (0 : ℝ) 1 → F.Apriori C τ)
    {s : ℝ} (hs : s∈Icc (0 : ℝ) 1) : F.Stable s := by
  let h:=1/(2*C*(F.gain+1))
  have hg:=F.gain_nonneg
  have hd : 0<2*C*(F.gain+1):=by positivity
  have hh : 0<h:=one_div_pos.mpr hd
  have he : (2*C*(F.gain+1))*h=1:=mul_one_div_cancel hd.ne'
  have hsmall : C*F.gain*h≤1/2:=by
    have hp : 0≤C*h:=mul_nonneg hC.le hh.le
    nlinarith
  let τ (n : ℕ):=min s ((n : ℝ)*h)
  have hτ (n : ℕ) : τ n∈Icc (0 : ℝ) 1:=
    ⟨le_min hs.1 (mul_nonneg (Nat.cast_nonneg _) hh.le),(min_le_left _ _).trans hs.2⟩
  have hτstep (n : ℕ) : |τ (n+1)-τ n|≤h:=by
    have hmono : τ n≤τ (n+1):=by
      apply min_le_min_left
      push_cast
      nlinarith
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    by_cases hsat : s≤(n : ℝ)*h
    · have hsat' : s≤((n+1 : ℕ) : ℝ)*h:=by push_cast; nlinarith
      simp only [τ,min_eq_left hsat,min_eq_left hsat',sub_self]
      exact hh.le
    · have hn : (n : ℝ)*h≤s:=(lt_of_not_ge hsat).le
      have hup:=min_le_right s (((n+1 : ℕ) : ℝ)*h)
      dsimp only [τ]
      rw [min_eq_right hn]
      push_cast at hup ⊢
      linarith
  have hstable (n : ℕ) : F.Stable (τ n):=by
    induction n with
    | zero =>
      simpa only [τ,Nat.cast_zero,zero_mul,min_eq_right hs.1] using F.stable_zero
    | succ n ih =>
      apply F.stable_step hC ih (ha (τ n) (hτ n))
      calc
        _≤C*F.gain*h:=mul_le_mul_of_nonneg_left (hτstep n)
          (mul_nonneg hC.le F.gain_nonneg)
        _≤1/2:=hsmall
  obtain ⟨n,hn⟩:=exists_nat_gt (s/h)
  have hsn : s≤(n : ℝ)*h:=by
    have hm:=(div_lt_iff₀ hh).mp hn
    linarith
  simpa only [τ,min_eq_left hsn] using hstable n

/-- The homotopy conclusion retains the original a priori constant. -/
theorem uniform_bound_of_apriori {C : ℝ} (hC : 0<C)
    (ha : ∀ τ : ℝ,τ∈Icc (0 : ℝ) 1 → F.Apriori C τ)
    {τ : ℝ} (hτ : τ∈Icc (0 : ℝ) 1) (f : ℕ → E) (hf : SquareSummable f) :
    SquareSummable (F.run τ f) ∧ sequenceNorm (F.run τ f)≤C*sequenceNorm f := by
  have hx:=F.stable_of_apriori hC ha hτ f hf
  exact ⟨hx,ha τ hτ f hf hx⟩

end CausalFeedback

namespace CausalFeedback
variable (F : CausalFeedback E)

theorem plant_squareSummable {x : ℕ → E} (hx : SquareSummable x) :
    SquareSummable (F.plant x) := by
  apply squareSummable_of_prefix_bound (C:=F.gain*sequenceNorm x)
  intro N
  exact (F.prefix_gain x N).trans
    (mul_le_mul_of_nonneg_left (prefixNorm_le_sequenceNorm hx N) F.gain_nonneg)

theorem plant_norm_bound {x : ℕ → E} (hx : SquareSummable x) :
    sequenceNorm (F.plant x)≤F.gain*sequenceNorm x :=
  sequenceNorm_le_of_prefix_bound (mul_nonneg F.gain_nonneg (sequenceNorm_nonneg x))
    (fun N => (F.prefix_gain x N).trans
      (mul_le_mul_of_nonneg_left (prefixNorm_le_sequenceNorm hx N) F.gain_nonneg))

def plantLinear : SequenceSpace E →ₗ[ℝ] SequenceSpace E where
  toFun x:=toL2 (F.plant x) (F.plant_squareSummable (lp_squareSummable x))
  map_add' x y:=by
    apply Subtype.ext
    exact F.plant.map_add x y
  map_smul' r x:=by
    apply Subtype.ext
    exact F.plant.map_smul r x

def plantL2 : SequenceSpace E →L[ℝ] SequenceSpace E :=
  F.plantLinear.mkContinuous F.gain (fun x => by
    rw [lp_norm_eq_sequenceNorm,lp_norm_eq_sequenceNorm]
    exact F.plant_norm_bound (lp_squareSummable x))

@[simp] theorem plantL2_apply (x : SequenceSpace E) (k : ℕ) : F.plantL2 x k=F.plant x k := rfl

theorem plantL2_norm_le : ‖F.plantL2‖≤F.gain := by
  apply F.plantL2.opNorm_le_bound F.gain_nonneg
  intro x
  rw [lp_norm_eq_sequenceNorm,lp_norm_eq_sequenceNorm]
  exact F.plant_norm_bound (lp_squareSummable x)

theorem delta_squareSummable {x : ℕ → E} (hx : SquareSummable x) :
    SquareSummable (F.delta x) :=
  squareSummable_of_prefix_bound (fun N =>
    (F.delta_prefix_bound x N).trans (prefixNorm_le_sequenceNorm hx N))

def deltaL2 (x : SequenceSpace E) : SequenceSpace E :=
  toL2 (F.delta x) (F.delta_squareSummable (lp_squareSummable x))

@[simp] theorem deltaL2_apply (x : SequenceSpace E) (k : ℕ) : F.deltaL2 x k=F.delta x k := rfl

theorem deltaL2_norm_le (x : SequenceSpace E) : ‖F.deltaL2 x‖≤‖x‖ := by
  rw [lp_norm_eq_sequenceNorm,lp_norm_eq_sequenceNorm]
  exact sequenceNorm_le_of_prefix_bound (sequenceNorm_nonneg _)
    (fun N => (F.delta_prefix_bound x N).trans
      (prefixNorm_le_sequenceNorm (lp_squareSummable x) N))

theorem run_toL2_equation (τ : ℝ) (f : ℕ → E) (hf : SquareSummable f)
    (hx : SquareSummable (F.run τ f)) :
    toL2 (F.run τ f) hx=
      F.plantL2 (τ • F.deltaL2 (toL2 (F.run τ f) hx))+toL2 f hf := by
  apply Subtype.ext
  exact F.run_equation τ f

end CausalFeedback

namespace CausalFeedback
variable (F : CausalFeedback E) (B : BilinearIQC (SequenceSpace E))
variable {M ε : ℝ} (hM : ‖B‖≤M) (hε : 0<ε)
variable (hneg : ∀ z : SequenceSpace E,iqcValue B (F.plantL2 z) z≤ -ε*‖z‖^2)
variable (hpos : ∀ τ : ℝ,τ∈Icc (0 : ℝ) 1 → ∀ x : SequenceSpace E,
  0≤ iqcValue B x (τ • F.deltaL2 x))
include B hM hε hneg hpos

theorem iqc_apriori (τ : ℝ) (hτ : τ∈Icc (0 : ℝ) 1) :
    F.Apriori (aprioriConstant M F.gain ε) τ := by
  intro f hf hx
  have h:=uniform_apriori_bound B F.plantL2 hM F.plantL2_norm_le hε hneg
    (toL2 (F.run τ f) hx) (τ • F.deltaL2 (toL2 (F.run τ f) hx)) (toL2 f hf)
    (F.run_toL2_equation τ f hf hx) (hpos τ hτ _)
  simpa only [toL2_norm] using h

theorem iqc_uniform_bound {τ : ℝ} (hτ : τ∈Icc (0 : ℝ) 1)
    (f : ℕ → E) (hf : SquareSummable f) :
    SquareSummable (F.run τ f) ∧
      sequenceNorm (F.run τ f)≤aprioriConstant M F.gain ε*sequenceNorm f :=
  F.uniform_bound_of_apriori
    (aprioriConstant_pos ((norm_nonneg B).trans hM) F.gain_nonneg hε)
    (fun τ hτ => F.iqc_apriori B hM hε hneg hpos τ hτ) hτ f hf

end CausalFeedback

end
end nesterov.IQC
