import polyak.Numerics.Parametric.DyadicCheck
import polyak.Numerics.Parametric.Memo

/-!
Article: Appendix B, correlated parameter residual bounds.
Use: precondition the parameter derivative before multiplying by I−mid(I).
This retains cancellation between equations in ill-conditioned source systems.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def correlatedResidual {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : DyadicConfig) :
    Fin n → IntervalRat := fun i =>
  IntervalRat.add
    (intervalRatMatVec Y (fun j => outcome
      (dyadicValue (F j) (pointIntervalEnv (Fin.cons I.midpoint m)) cfg)) i)
    (IntervalRat.mul (IntervalRat.sub I (IntervalRat.singleton I.midpoint))
      (intervalRatMatVec Y (fun j => outcome (dyadicDerivative (F j)
        (finBoxEnv (box I (fun k => IntervalRat.singleton (m k)))) 0 cfg)) i))

def correlatedCenterImage {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : DyadicConfig) :
    Fin n → IntervalRat := fun i =>
  IntervalRat.sub (IntervalRat.singleton (m i)) (correlatedResidual F I m Y cfg i)

noncomputable section

theorem correlatedResidual_mem {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i, ADSupported (F i)) (I : IntervalRat) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : DyadicConfig)
    (hok : dyadicResidualSucceeded F I m cfg=true) {s : ℝ} (hs : s∈I) (i : Fin n) :
    ∑ j,(Y i j : ℝ)*system F s (fun k => (m k : ℝ)) j∈correlatedResidual F I m Y cfg i := by
  simp only [dyadicResidualSucceeded,Bool.and_eq_true,decide_eq_true_eq] at hok
  let mr : Fin n → ℝ := fun k => (m k : ℝ)
  have hd (r : ℝ) : HasDerivAt
      (fun r => ∑ j,(Y i j : ℝ)*eval (F j) r mr)
      (∑ j,(Y i j : ℝ)*deriv (fun r => eval (F j) r mr) r) r := by
    exact HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
      ((parameter_differentiable (F j) (hF j) mr).differentiableAt.hasDerivAt (x:=r)).const_mul (Y i j : ℝ))
  change (∑ j,(Y i j : ℝ)*eval (F j) s mr)∈_
  unfold correlatedResidual
  apply meanValue_enclosure (f:=fun r => ∑ j,(Y i j : ℝ)*eval (F j) r mr) I.midpoint_mem
  · apply mem_interval_sum Finset.univ
      (fun j => (Y i j : ℝ)*eval (F j) I.midpoint mr)
      (fun j => IntervalRat.scale (Y i j) (outcome
        (dyadicValue (F j) (pointIntervalEnv (Fin.cons I.midpoint m)) cfg)))
    intro j _
    apply IntervalRat.mem_scale
    apply dyadicValue_mem (F j) _ cfg hok.1
      (finEnv (embed (I.midpoint : ℝ) mr)) _ (hok.2 j).1
    have he : finEnv (embed (I.midpoint : ℝ) mr)=
        finEnv (fun k : Fin (n+1) => ((Fin.cons (α := fun _ : Fin (n+1) => ℚ)
          I.midpoint m k : ℚ) : ℝ)) := by
      congr 1
      funext k
      refine Fin.cases ?_ (fun l => ?_) k <;> simp [embed,mr]
    rw [he]
    exact finEnv_ratCast_mem_pointIntervalEnv _
  · exact fun r _ => (hd r).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [(hd r).deriv]
    apply mem_interval_sum Finset.univ
      (fun j => (Y i j : ℝ)*deriv (fun r => eval (F j) r mr) r)
      (fun j => IntervalRat.scale (Y i j) (outcome (dyadicDerivative (F j)
        (finBoxEnv (box I (fun k => IntervalRat.singleton (m k)))) 0 cfg)))
    intro j _
    apply IntervalRat.mem_scale
    rw [← parameter_evalAlong (F j) r]
    apply dyadicDerivative_mem (F j) _ 0 cfg (finEnv (embed r mr))
      (finEnv_mem_finBoxEnv (embed_mem_box hr (fun k => IntervalRat.mem_singleton (m k)))) r
    · simpa [finBoxEnv,box] using hr
    · exact (hok.2 j).2
  · exact hs

theorem correlatedCenterImage_mem {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i, ADSupported (F i)) (I : IntervalRat) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : DyadicConfig)
    (hok : dyadicResidualSucceeded F I m cfg=true) {s : ℝ} (hs : s∈I) (i : Fin n) :
    newton (Y.map fun q => (q : ℝ)) F s (fun k => (m k : ℝ)) i∈
      correlatedCenterImage F I m Y cfg i :=
  IntervalRat.mem_sub (IntervalRat.mem_singleton (m i))
    (correlatedResidual_mem F hF I m Y cfg hok hs i)

end

def correlatedWeightedCenter {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig) : Fin n → IntervalRat :=
  correlatedCenterImage (scaledSystem F cert.center cert.radius) I
    (normalized cert).center (normalized cert).preconditioner cfg

def checkCorrelated {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig := {}) : Bool :=
  decide (∀ i,(F i).checkADSupported=true) &&
    dyadicJacobianSucceeded (scaledSystem F cert.center cert.radius) I (unitBox n) cfg &&
    dyadicResidualSucceeded (scaledSystem F cert.center cert.radius) I (normalized cert).center cfg &&
    weightedEnclosureCheck cert (memoMatrix (dyadicWeightedJacobian F I cert cfg))
      (memoFin (correlatedWeightedCenter F I cert cfg))

noncomputable section

theorem checkCorrelated_sound {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig)
    (hc : checkCorrelated F I cert cfg=true) :
    ∀ s∈I, ∃! x, FinBoxMem x (coordinateBox cert.center cert.radius) ∧ system F s x=0 := by
  simp only [checkCorrelated,memoMatrix_eq,memoFin_eq,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hF,hJ⟩,hC⟩,hcheck⟩ := hc
  have hF' : ∀ i, ADSupported (F i) := fun i => ((F i).checkADSupported_eq_true_iff).mp (hF i)
  have hscaled : ∀ i, ADSupported (scaledSystem F cert.center cert.radius i) :=
    fun i => substitute_supported _ (scaledVariable_supported cert.center cert.radius) _ (hF' i)
  apply weightedEnclosureCheck_sound F hF' I cert _ _ _ _ hcheck
  · intro s hs x hx i j
    exact dyadicJacobian_mem _ hscaled I (unitBox n) cfg hJ hs hx i j
  · intro s hs i
    exact correlatedCenterImage_mem _ hscaled I (normalized cert).center
      (normalized cert).preconditioner cfg hC hs i

end
end polyak.Numerics.Parametric
