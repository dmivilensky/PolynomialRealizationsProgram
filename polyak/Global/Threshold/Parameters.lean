import polyak.Global.Threshold.KappaMonotonicity
import Mathlib.Topology.Instances.EReal.Lemmas

/-! The actual two-dimensional strip and the original tuning chart. The
extended condition-number target carries the standard order topology. -/
noncomputable section
namespace polyak.Global.Threshold
open General Levels Set

abbrev ParameterStrip := {p : ℝ×ℝ // 0≤p.2 ∧ p.2<1 ∧ 0<p.1 ∧ p.1<2*(1+p.2)}
abbrev ConditionNumber := Set.Ioi (1:ℝ)
abbrev ExtendedConditionNumber := Set.Ioi (1:EReal)

def tuning (p : ParameterStrip) (κ : ConditionNumber) : Tuning where
  kappa:=κ.val
  y:=p.val.1
  beta:=p.val.2
  kappa_gt_one:=κ.property
  beta_nonneg:=p.property.1
  beta_lt_one:=p.property.2.1
  y_pos:=p.property.2.2.1
  y_lt:=p.property.2.2.2

def parameters (q : Tuning) : ParameterStrip :=
  ⟨(q.y,q.beta),q.beta_nonneg,q.beta_lt_one,q.y_pos,q.y_lt⟩

def conditionNumber (q : Tuning) : ConditionNumber:=⟨q.kappa,q.kappa_gt_one⟩

@[simp] theorem tuning_parameters (q : Tuning) : tuning (parameters q) (conditionNumber q)=q := by
  cases q
  rfl

@[fun_prop] theorem continuous_tuning : Continuous (fun p : ParameterStrip×ConditionNumber=>tuning p.1 p.2) := by
  apply continuous_induced_rng.mpr
  exact (continuous_subtype_val.comp continuous_snd).prodMk
    (((continuous_fst.comp continuous_subtype_val).comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_subtype_val).comp continuous_fst))

@[fun_prop] theorem continuous_parameters : Continuous parameters := by
  exact (Tuning.continuous_y.prodMk Tuning.continuous_beta).subtype_mk _

@[fun_prop] theorem continuous_conditionNumber : Continuous conditionNumber :=
  Tuning.continuous_kappa.subtype_mk _

def fixedThreshold (p : ParameterStrip) (κ : ConditionNumber) : ℝ:=sigma (tuning p κ)
def fixedPeriodicThreshold (k : ℕ) (p : ParameterStrip) (κ : ConditionNumber) : ℝ:=sigmaPeriodic (tuning p κ) k

 theorem fixedThreshold_strictAnti (p : ParameterStrip) : StrictAnti (fixedThreshold p) := by
  intro a b hab
  exact sigma_strictAnti_kappa (tuning p a) (tuning p b) rfl rfl hab

 theorem fixedPeriodicThreshold_strictAnti (p : ParameterStrip) {k : ℕ} (hk : 3≤k) :
    StrictAnti (fixedPeriodicThreshold k p) := by
  intro a b hab
  exact sigmaPeriodic_strictAnti_kappa (tuning p a) (tuning p b) rfl rfl hab hk

@[fun_prop] theorem continuous_fixedPeriodicThreshold {k : ℕ} (hk : 3≤k) :
    Continuous (fun p : ParameterStrip×ConditionNumber=>fixedPeriodicThreshold k p.1 p.2) :=
  (continuous_sigmaPeriodic hk).comp continuous_tuning

end polyak.Global.Threshold
