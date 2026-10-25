import polyak.FareyPlateau.Plateau.RegularAdmissible
import polyak.FareyPlateau.Ray.Regularity
import polyak.FareyPlateau.Ray.Infimum

/-! The source a_F infimum includes the actual dual symbol of every
regular singleton, and strict regularity forces a>a_F. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Set
open scoped BigOperators

def regularSourceCertificate {q : Tuning} {L j k : ℕ}
    (R : RegularData q 0 L) (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hS : Set.range R.atoms={Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le})
    {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    Ray.SourceCertificate j k b D where
  card := Fintype.card R.lags
  lag i := ((Fintype.equivFin R.lags).symm i:ℤ)
  weight i := R.dual ((Fintype.equivFin R.lags).symm i)
  admissible := (regular_singleton_admissible R hk hj hjk b hb0 hbk hb hS he).reindex
    (Fintype.equivFin R.lags).symm

theorem regularSourceCertificate_symbol {q : Tuning} {L j k : ℕ}
    (R : RegularData q 0 L) (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hS : Set.range R.atoms={Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le})
    {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    LargeCurvature.indexedSymbol q 0 (regularSourceCertificate R hk hj hjk b hb0 hbk hb hS he).lag
      (regularSourceCertificate R hk hj hjk b hb0 hbk hb hS he).weight=
        finiteSymbol q 0 R.lags R.dual := by
  classical
  funext x
  change (∑i,R.dual ((Fintype.equivFin R.lags).symm i)*
    lagExtension q 0 ((Fintype.equivFin R.lags).symm i:ℤ) x)=_
  rw [(Fintype.equivFin R.lags).symm.sum_comp
    (fun n : R.lags=>R.dual n*lagExtension q 0 (n:ℤ) x)]
  exact Finset.sum_coe_sort R.lags (fun n=>R.dual n*lagExtension q 0 n x)

theorem regularSourceCertificate_maximum_lt {q : Tuning} {L j k : ℕ}
    (R : RegularData q 0 L) (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hS : Set.range R.atoms={Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le})
    {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    (regularSourceCertificate R hk hj hjk b hb0 hbk hb hS he).maximum<a := by
  classical
  let C := regularSourceCertificate R hk hj hjk b hb0 hbk hb hS he
  have hbinv : (b*j)%k=1 := by
    simpa only [Int.ModEq,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1)
      (by omega : (1:ℤ)<k)] using hb
  apply (C.ray_criterion hj hjk hbinv q he).mpr
  have hfun : LargeCurvature.indexedSymbol q 0 C.lag C.weight=finiteSymbol q 0 R.lags R.dual :=
    regularSourceCertificate_symbol R hk hj hjk b hb0 hbk hb hS he
  rw [hfun]
  refine ⟨?_,?_,?_⟩
  · intro x hx hxπ hne
    exact R.dual_strict x hx hxπ (fun i hh=>hne (hh.trans
      (congrArg Subtype.val (RegularSingleton.atoms_eq R hk hjk hS i))))
  · have hh := R.support_curvature ⟨0,R.d_pos⟩
    rw [RegularSingleton.atoms_eq R hk hjk hS,Ray.source_atom_value] at hh
    exact hh
  · change 0<∑i,R.dual ((Fintype.equivFin R.lags).symm i)*
      (((Fintype.equivFin R.lags).symm i:ℤ):ℝ)*
      ((((Fintype.equivFin R.lags).symm i:ℤ):ℝ)+2*Geometry.tau q)
    rw [(Fintype.equivFin R.lags).symm.sum_comp
      (fun n : R.lags=>R.dual n*((n:ℤ):ℝ)*(((n:ℤ):ℝ)+2*Geometry.tau q)),
      Finset.sum_coe_sort R.lags (fun n=>R.dual n*(n:ℝ)*((n:ℝ)+2*Geometry.tau q))]
    exact R.endpoint_curvature

theorem regular_singleton_aF_lt {q : Tuning} {L j k : ℕ}
    (R : RegularData q 0 L) (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hS : Set.range R.atoms={Edge.atom j k (lt_of_lt_of_le (by decide : 0<3) hk) hjk.le})
    {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    Ray.aF j k b D<a := by
  let C := regularSourceCertificate R hk hj hjk b hb0 hbk hb hS he
  exact (Ray.aF_le_maximum C hj hjk (by
    simpa only [Int.ModEq,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1)
      (by omega : (1:ℤ)<k)] using hb)).trans_lt
    (regularSourceCertificate_maximum_lt R hk hj hjk b hb0 hbk hb hS he)

end polyak.FareyPlateau
