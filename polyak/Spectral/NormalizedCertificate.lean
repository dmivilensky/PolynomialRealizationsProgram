import polyak.Spectral.CompactDual
import polyak.Duality.Certificate

/-!
Article: Appendix A, normalized finite strict certificates and their compact limiting hull.
Use: every actual certificate yields a zero-charge point of one fixed compact convex set.
Proof: multiply each lag weight by its positive sinh denominator, normalize total mass,
and preserve the exact raw symbol under the resulting convex combination.
-/

namespace polyak.Spectral
noncomputable section
open Set Filter Duality
open scoped Topology OnePoint

/-- Article: the physical cosine coordinate as a point of the common complex window. -/
def dualAngle (s : ℝ) (hs : 0<s) (c : Frequency) : lagWindow s :=
  ⟨(Real.arccos c : ℂ),interior_subset (real_mem_interior_lagWindow hs
    ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩)⟩

/-- Article: two minimizer signs and both signs of every finite lag. -/
abbrev CertificateIndices {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s) :=
  Bool ⊕ ((↑cert.lags) × Bool)

/-- Article: unnormalized mass in the compactified symbol family. -/
def certificateMass {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s) :
    CertificateIndices cert → ℝ
  | .inl false => cert.γplus
  | .inl true => cert.γminus
  | .inr (n,false) => cert.α n*Real.sinh ((n : ℕ)*s)
  | .inr (n,true) => cert.β n*Real.sinh ((n : ℕ)*s)

/-- Article: each normalized mass is nonnegative. -/
theorem certificateMass_nonneg {m : C(Frequency,ℂ)} {s : ℝ}
    (cert : StrictCertificate m s) (hs : 0<s) (i : CertificateIndices cert) :
    0 ≤ certificateMass cert i := by
  rcases i with b | ⟨n,b⟩ <;> cases b
  · exact cert.γplus_nonneg
  · exact cert.γminus_nonneg
  · exact mul_nonneg (cert.α_nonneg n n.property)
      (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n n.property)) hs)).le
  · exact mul_nonneg (cert.β_nonneg n n.property)
      (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n n.property)) hs)).le

/-- Article: strict separation forces positive total mass. Use: justify normalization without an assumed nonzero certificate. -/
theorem certificateMass_sum_pos {m : C(Frequency,ℂ)} {s : ℝ}
    (cert : StrictCertificate m s) (hs : 0<s) : 0<∑ i,certificateMass cert i := by
  have hnonneg : 0 ≤ ∑ i,certificateMass cert i := Finset.sum_nonneg (fun i _ => certificateMass_nonneg cert hs i)
  by_contra hnot
  have hz : ∑ i,certificateMass cert i=0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hall : ∀ i,certificateMass cert i=0 := by
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => certificateMass_nonneg cert hs i)).mp hz i
      (Finset.mem_univ _)
  have hgp : cert.γplus=0 := hall (.inl false)
  have hgm : cert.γminus=0 := hall (.inl true)
  have hα (n : ℕ) (hn : n∈cert.lags) : cert.α n=0 := by
    have he := hall (.inr (⟨n,hn⟩,false))
    have hp := Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n hn)) hs)
    exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hp)
  have hβ (n : ℕ) (hn : n∈cert.lags) : cert.β n=0 := by
    have he := hall (.inr (⟨n,hn⟩,true))
    have hp := Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n hn)) hs)
    exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hp)
  let c : Frequency := ⟨0,by norm_num⟩
  have hsym : symbol m s cert.lags cert.α cert.β cert.γplus cert.γminus c=0 := by
    unfold symbol
    rw [hgp,hgm]
    simp only [zero_mul,add_zero]
    apply Finset.sum_eq_zero
    intro n hn
    rw [hα n hn,hβ n hn]
    ring
  have hbad := cert.strict c
  rw [hsym] at hbad
  linarith [cert.ε_pos]

/-- Article: the correct compactified generator for every finite certificate constraint. -/
def certificateGenerator {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) : CertificateIndices cert → DualCoefficient s
  | .inl false => coefficientFamily s 1 hs (by norm_num) ∞
  | .inl true => coefficientFamily s (-1) hs (by norm_num) ∞
  | .inr (n,false) => coefficientFamily s 1 hs (by norm_num) ((n.val-1 : ℕ) : OnePoint ℕ)
  | .inr (n,true) => coefficientFamily s (-1) hs (by norm_num) ((n.val-1 : ℕ) : OnePoint ℕ)

/-- Article: every selected generator belongs to the same fixed compact family. -/
theorem certificateGenerator_mem {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) (i : CertificateIndices cert) : certificateGenerator cert hs i∈dualGenerators s hs := by
  rcases i with b | ⟨n,b⟩ <;> cases b
  · exact Or.inl ⟨∞,rfl⟩
  · exact Or.inr ⟨∞,rfl⟩
  · exact Or.inl ⟨_,rfl⟩
  · exact Or.inr ⟨_,rfl⟩

/-- Article: real symbol evaluation is a real linear functional of all stored coefficients. -/
def evaluateDualReal {s : ℝ} (u : ℝ) (z : lagWindow s) : DualCoefficient s →ₗ[ℝ] ℝ :=
  (dualTraceCLM u z).toLinearMap

/-- Article: minimizer generator evaluation. -/
theorem evaluateDualReal_star {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) (u : ℝ) (c : Frequency) (b : Bool) :
    evaluateDualReal u (dualAngle s hs c) (certificateGenerator cert hs (.inl b))=g u c := by
  cases b <;> change (evaluateDual u (coefficientFamily s _ hs _ ∞) (dualAngle s hs c)).re=g u c
  all_goals rw [evaluateDual_coefficient_infty]
  all_goals change (complexGap u (Real.arccos c : ℂ)).re=g u c
  all_goals
    rw [complexGap,← Complex.ofReal_cos,Real.cos_arccos c.property.1 c.property.2]
    simp only [Complex.sub_re,Complex.one_re,← Complex.ofReal_pow,Complex.ofReal_re,g]

/-- Article: finite-lag generator evaluation. -/
theorem evaluateDualReal_lag {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) (u : ℝ) (c : Frequency) (n : ↑cert.lags) (b : Bool) :
    evaluateDualReal u (dualAngle s hs c) (certificateGenerator cert hs (.inr (n,b)))=
      (if b then (lagA u s n c+lagB u n c)/Real.sinh ((n : ℕ)*s)
        else (lagA u s n c-lagB u n c)/Real.sinh ((n : ℕ)*s)) := by
  have hn : n.val-1+1=n.val := Nat.sub_add_cancel (cert.positive_lag n n.property)
  cases b
  · change (evaluateDual u (coefficientFamily s 1 hs _ ((n.val-1 : ℕ) : OnePoint ℕ)) (dualAngle s hs c)).re=_
    rw [evaluateDual_coefficient_coe]
    change (complexLag u s 1 (n.val-1) (Real.arccos c : ℂ)).re=_
    rw [complexLag_arccos u s 1 (n.val-1) hs c,hn]
    simp only [Complex.ofReal_re,one_mul,Bool.false_eq_true,↓reduceIte]
  · change (evaluateDual u (coefficientFamily s (-1) hs _ ((n.val-1 : ℕ) : OnePoint ℕ)) (dualAngle s hs c)).re=_
    rw [evaluateDual_coefficient_coe]
    change (complexLag u s (-1) (n.val-1) (Real.arccos c : ℂ)).re=_
    rw [complexLag_arccos u s (-1) (n.val-1) hs c,hn]
    simp only [Complex.ofReal_re,neg_one_mul,sub_neg_eq_add,↓reduceIte]

/-- Article: the common C charge of each signed generator. -/
def certificateSign {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s) : CertificateIndices cert → ℝ
  | .inl b => if b then -1 else 1
  | .inr (_,b) => if b then -1 else 1

/-- Article: exact generator charge. -/
theorem certificateGenerator_charge {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) (i : CertificateIndices cert) :
    (certificateGenerator cert hs i).1=certificateSign cert i := by
  rcases i with b | ⟨n,b⟩ <;> cases b <;> rfl

/-- Article: the unnormalized finite dual combination. -/
def certificateCombination {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) : DualCoefficient s := ∑ i,certificateMass cert i • certificateGenerator cert hs i

/-- Article: raw certificate cancellation survives radial normalization exactly. -/
theorem certificateCombination_charge {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) : (certificateCombination cert hs).1=0 := by
  unfold certificateCombination
  rw [Prod.fst_sum]
  simp only [Prod.smul_fst,certificateGenerator_charge,smul_eq_mul,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,certificateMass,certificateSign,
    Bool.false_eq_true,↓reduceIte,mul_neg_one,mul_one]
  have hsum : (∑ n : ↑cert.lags, (-(cert.β n*Real.sinh ((n : ℕ)*s))+cert.α n*Real.sinh ((n : ℕ)*s)))=
      ∑ n ∈ cert.lags,(cert.α n-cert.β n)*Real.sinh (n*s) := by
    calc
      _ = ∑ n : ↑cert.lags,(cert.α n-cert.β n)*Real.sinh ((n : ℕ)*s) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := Finset.sum_coe_sort cert.lags
        (fun n : ℕ => (cert.α n-cert.β n)*Real.sinh ((n : ℝ)*s))

  rw [hsum]
  linarith [cert.cancel]

/-- Article: raw pointwise symbol in the polynomial twist coordinate. -/
def rawCoefficientSymbol {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (u : ℝ) (c : Frequency) : ℝ :=
  (∑ n ∈ cert.lags,(cert.α n*(lagA u s n c-lagB u n c)+cert.β n*(lagA u s n c+lagB u n c)))+
    (cert.γplus+cert.γminus)*g u c

/-- Article: radial normalization preserves the actual raw symbol. -/
theorem evaluateDualReal_combination {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) (u : ℝ) (c : Frequency) :
    evaluateDualReal u (dualAngle s hs c) (certificateCombination cert hs)=rawCoefficientSymbol cert u c := by
  unfold certificateCombination
  rw [map_sum]
  simp only [map_smul,smul_eq_mul,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
    certificateMass,evaluateDualReal_star,evaluateDualReal_lag,Bool.false_eq_true,↓reduceIte]
  have hsum : (∑ n : ↑cert.lags,(
      (cert.β n*Real.sinh ((n : ℕ)*s))*((lagA u s n c+lagB u n c)/Real.sinh ((n : ℕ)*s))+
      (cert.α n*Real.sinh ((n : ℕ)*s))*((lagA u s n c-lagB u n c)/Real.sinh ((n : ℕ)*s))))=
      ∑ n ∈ cert.lags,(cert.α n*(lagA u s n c-lagB u n c)+cert.β n*(lagA u s n c+lagB u n c)) := by
    calc
      _ = ∑ n : ↑cert.lags,(cert.α n*(lagA u s n c-lagB u n c)+cert.β n*(lagA u s n c+lagB u n c)) := by
        apply Finset.sum_congr rfl
        intro n _
        have hp : Real.sinh ((n : ℕ)*s)≠0 := ne_of_gt
          (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n n.property)) hs))
        field_simp
        ring
      _ = _ := Finset.sum_coe_sort cert.lags
        (fun n : ℕ => cert.α n*(lagA u s n c-lagB u n c)+cert.β n*(lagA u s n c+lagB u n c))

  rw [hsum]
  unfold rawCoefficientSymbol
  ring

/-- Article: the raw duality symbol and the twist-coordinate symbol coincide. -/
theorem rawCoefficientSymbol_eq {u s : ℝ}
    (cert : StrictCertificate (Waves.polyakMultiplier (Real.arsinh u)) s) (c : Frequency) :
    rawCoefficientSymbol cert u c=
      symbol (Waves.polyakMultiplier (Real.arsinh u)) s cert.lags cert.α cert.β cert.γplus cert.γminus c := by
  have hg : Duality.g (Waves.polyakMultiplier (Real.arsinh u)) c=g u c := by
    simp only [Duality.g,Waves.polyakMultiplier_normSq,Real.sinh_arsinh,g]
    ring
  have ha (n : ℕ) : Duality.a (Waves.polyakMultiplier (Real.arsinh u)) s n c=lagA u s n c := by
    simp only [Duality.a,hg,lagA,lagD,Waves.chebT_arccos]
  have hb (n : ℕ) (hn : 1 ≤ n) : Duality.b (Waves.polyakMultiplier (Real.arsinh u)) n c=lagB u n c := by
    exact Waves.polyak_skew (Real.arsinh u) n hn c |>.trans (by rw [Real.sinh_arsinh])
  unfold rawCoefficientSymbol symbol
  rw [hg]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [ha n,hb n (cert.positive_lag n hn)]

/-- Article: normalized finite certificate in the compact hull. -/
def normalizedCertificate {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) : DualCoefficient s :=
  (∑ i,certificateMass cert i)⁻¹ • certificateCombination cert hs

/-- Article: actual convex-hull membership of every normalized finite certificate. -/
theorem normalizedCertificate_mem {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) : normalizedCertificate cert hs∈dualHull s hs := by
  have hp := certificateMass_sum_pos cert hs
  have he : normalizedCertificate cert hs=
      ∑ i,(certificateMass cert i/(∑ j,certificateMass cert j)) • certificateGenerator cert hs i := by
    unfold normalizedCertificate certificateCombination
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    ring
  rw [he]
  apply sum_mem_dualHull
  · intro i
    exact div_nonneg (certificateMass_nonneg cert hs i) hp.le
  · rw [← Finset.sum_div,div_self (ne_of_gt hp)]
  · exact certificateGenerator_mem cert hs

/-- Article: normalized certificates retain zero charge. -/
theorem normalizedCertificate_charge {m : C(Frequency,ℂ)} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0<s) : (normalizedCertificate cert hs).1=0 := by
  simp only [normalizedCertificate,Prod.smul_fst,certificateCombination_charge,smul_zero]

/-- Article: exact normalized pointwise symbol, including its strictly positive total mass denominator. -/
theorem normalizedCertificate_evaluate {u s : ℝ}
    (cert : StrictCertificate (Waves.polyakMultiplier (Real.arsinh u)) s) (hs : 0<s) (c : Frequency) :
    (evaluateDual u (normalizedCertificate cert hs) (dualAngle s hs c)).re=
      symbol (Waves.polyakMultiplier (Real.arsinh u)) s cert.lags cert.α cert.β cert.γplus cert.γminus c /
        (∑ i,certificateMass cert i) := by
  change evaluateDualReal u (dualAngle s hs c) (normalizedCertificate cert hs)=_
  rw [normalizedCertificate,map_smul,evaluateDualReal_combination,rawCoefficientSymbol_eq]
  simp only [smul_eq_mul]
  ring

/-- Article: every actual strict certificate gives a nonpositive zero-charge point in the fixed compact hull. -/
theorem _root_.polyak.Duality.StrictCertificate.exists_normalized_dual {u s : ℝ}
    (cert : StrictCertificate (Waves.polyakMultiplier (Real.arsinh u)) s) (hs : 0<s) :
    ∃ d∈dualHull s hs,d.1=0 ∧ ∀ c : Frequency,(evaluateDual u d (dualAngle s hs c)).re ≤ 0 := by
  refine ⟨normalizedCertificate cert hs,normalizedCertificate_mem cert hs,normalizedCertificate_charge cert hs,fun c => ?_⟩
  rw [normalizedCertificate_evaluate]
  exact div_nonpos_of_nonpos_of_nonneg (le_trans (cert.strict c) (neg_nonpos.mpr cert.ε_pos.le))
    (certificateMass_sum_pos cert hs).le

end
end polyak.Spectral
