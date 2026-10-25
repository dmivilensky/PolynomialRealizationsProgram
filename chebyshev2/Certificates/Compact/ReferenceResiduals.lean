import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch000
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch001
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch002
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch003
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch004
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch005
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch006
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch007
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch008
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch009
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch010
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch011
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch012
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch013
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch014
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch015
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch016
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch017
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch018
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch019
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch020
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch021
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch022
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch023
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch024
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch025
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch026
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch027
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch028
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch029
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch030
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch031
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch032
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch033
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch034
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch035
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch036
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch037
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch038
import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Batch039
import chebyshev2.Certificates.Compact.ReferenceResidualData

/-!
Article: chebyshev2, Section 4.1.
Reference Residuals.
Use: `chebyshev2.Certificates.Compact.ReferenceResiduals.checks` feeds
`chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` (full trajectory).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace chebyshev2.Certificates.Compact.ReferenceResiduals
open chebyshev2.Numerics.IntegerCertificate
open chebyshev2.Numerics chebyshev2.Certificates.DualInputs
theorem combineChecked {as bs : List ResidualCell.Row}
    (ha : ∀ r∈as,ResidualCell.check scale ops piBounds eta r=true)
    (hb : ∀ r∈bs,ResidualCell.check scale ops piBounds eta r=true) :
    ∀ r∈as++bs,ResidualCell.check scale ops piBounds eta r=true := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · exact ha r h
  · exact hb r h

theorem checkedBlock (rs : List ResidualCell.Row)
    (h : rs.all (ResidualCell.check scale ops piBounds eta)=true) :
    ∀ r∈rs,ResidualCell.check scale ops piBounds eta r=true :=
  List.all_eq_true.mp h

theorem checks : ∀ r∈rows,ResidualCell.check scale ops piBounds eta r=true :=
  combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (combineChecked (checkedBlock block0 checks0) (checkedBlock block1 checks1)) (checkedBlock block2 checks2)) (checkedBlock block3 checks3)) (checkedBlock block4 checks4)) (checkedBlock block5 checks5)) (checkedBlock block6 checks6)) (checkedBlock block7 checks7)) (checkedBlock block8 checks8)) (checkedBlock block9 checks9)) (checkedBlock block10 checks10)) (checkedBlock block11 checks11)) (checkedBlock block12 checks12)) (checkedBlock block13 checks13)) (checkedBlock block14 checks14)) (checkedBlock block15 checks15)) (checkedBlock block16 checks16)) (checkedBlock block17 checks17)) (checkedBlock block18 checks18)) (checkedBlock block19 checks19)) (checkedBlock block20 checks20)) (checkedBlock block21 checks21)) (checkedBlock block22 checks22)) (checkedBlock block23 checks23)) (checkedBlock block24 checks24)) (checkedBlock block25 checks25)) (checkedBlock block26 checks26)) (checkedBlock block27 checks27)) (checkedBlock block28 checks28)) (checkedBlock block29 checks29)) (checkedBlock block30 checks30)) (checkedBlock block31 checks31)) (checkedBlock block32 checks32)) (checkedBlock block33 checks33)) (checkedBlock block34 checks34)) (checkedBlock block35 checks35)) (checkedBlock block36 checks36)) (checkedBlock block37 checks37)) (checkedBlock block38 checks38)) (checkedBlock block39 checks39)) (checkedBlock block40 checks40)) (checkedBlock block41 checks41)) (checkedBlock block42 checks42)) (checkedBlock block43 checks43)) (checkedBlock block44 checks44)) (checkedBlock block45 checks45)) (checkedBlock block46 checks46)) (checkedBlock block47 checks47)) (checkedBlock block48 checks48)) (checkedBlock block49 checks49)) (checkedBlock block50 checks50)) (checkedBlock block51 checks51)) (checkedBlock block52 checks52)) (checkedBlock block53 checks53)) (checkedBlock block54 checks54)) (checkedBlock block55 checks55)) (checkedBlock block56 checks56)) (checkedBlock block57 checks57)) (checkedBlock block58 checks58)) (checkedBlock block59 checks59)) (checkedBlock block60 checks60)) (checkedBlock block61 checks61)) (checkedBlock block62 checks62)) (checkedBlock block63 checks63)) (checkedBlock block64 checks64)) (checkedBlock block65 checks65)) (checkedBlock block66 checks66)) (checkedBlock block67 checks67)) (checkedBlock block68 checks68)) (checkedBlock block69 checks69)) (checkedBlock block70 checks70)) (checkedBlock block71 checks71)) (checkedBlock block72 checks72)) (checkedBlock block73 checks73)) (checkedBlock block74 checks74)) (checkedBlock block75 checks75)) (checkedBlock block76 checks76)) (checkedBlock block77 checks77)) (checkedBlock block78 checks78)) (checkedBlock block79 checks79)) (checkedBlock block80 checks80)) (checkedBlock block81 checks81)) (checkedBlock block82 checks82)) (checkedBlock block83 checks83)) (checkedBlock block84 checks84)) (checkedBlock block85 checks85)) (checkedBlock block86 checks86)) (checkedBlock block87 checks87)) (checkedBlock block88 checks88)) (checkedBlock block89 checks89)) (checkedBlock block90 checks90)) (checkedBlock block91 checks91)) (checkedBlock block92 checks92)) (checkedBlock block93 checks93)) (checkedBlock block94 checks94)) (checkedBlock block95 checks95)) (checkedBlock block96 checks96)) (checkedBlock block97 checks97)) (checkedBlock block98 checks98)) (checkedBlock block99 checks99)) (checkedBlock block100 checks100)) (checkedBlock block101 checks101)) (checkedBlock block102 checks102)) (checkedBlock block103 checks103)) (checkedBlock block104 checks104)) (checkedBlock block105 checks105)) (checkedBlock block106 checks106)) (checkedBlock block107 checks107)) (checkedBlock block108 checks108)) (checkedBlock block109 checks109)) (checkedBlock block110 checks110)) (checkedBlock block111 checks111)) (checkedBlock block112 checks112)) (checkedBlock block113 checks113)) (checkedBlock block114 checks114)) (checkedBlock block115 checks115)) (checkedBlock block116 checks116)) (checkedBlock block117 checks117)) (checkedBlock block118 checks118)) (checkedBlock block119 checks119)) (checkedBlock block120 checks120)) (checkedBlock block121 checks121)) (checkedBlock block122 checks122)) (checkedBlock block123 checks123)) (checkedBlock block124 checks124)) (checkedBlock block125 checks125)) (checkedBlock block126 checks126)) (checkedBlock block127 checks127)) (checkedBlock block128 checks128)) (checkedBlock block129 checks129)) (checkedBlock block130 checks130)) (checkedBlock block131 checks131)) (checkedBlock block132 checks132)) (checkedBlock block133 checks133)) (checkedBlock block134 checks134)) (checkedBlock block135 checks135)) (checkedBlock block136 checks136)) (checkedBlock block137 checks137)) (checkedBlock block138 checks138)) (checkedBlock block139 checks139)) (checkedBlock block140 checks140)) (checkedBlock block141 checks141)) (checkedBlock block142 checks142)) (checkedBlock block143 checks143)) (checkedBlock block144 checks144)) (checkedBlock block145 checks145)) (checkedBlock block146 checks146)) (checkedBlock block147 checks147)) (checkedBlock block148 checks148)) (checkedBlock block149 checks149)) (checkedBlock block150 checks150)) (checkedBlock block151 checks151)) (checkedBlock block152 checks152)) (checkedBlock block153 checks153)) (checkedBlock block154 checks154)) (checkedBlock block155 checks155)) (checkedBlock block156 checks156)) (checkedBlock block157 checks157)
theorem actual_rhs_residual {r : ResidualCell.Row} (hr : r∈rows)
    {x : ℝ} (hx : x∈Set.Icc (0:ℝ) 1)
    (ht : (ResidualCell.values scale r 0).eval x∈Set.Icc (0:ℝ) 1) :
    0≤(ResidualCell.values scale r 3).eval x ∧
    |(ReferenceJetSource.referenceData reference).normalizedVelocity ((ResidualCell.values scale r 0).eval x)*
      ((Real.pi^2/4)*(((ResidualCell.values scale r 0).eval x)*
        (ReferenceJetSource.referenceData reference).normalizedRoot ((ResidualCell.values scale r 0).eval x))^2-
        2*(ResidualCell.values scale r 3).eval x-(sigma:ℝ)*((ResidualCell.values scale r 3).eval x)^2)-
      (ResidualCell.values scale r 4).eval x|≤(eta:ℝ) :=
  ResidualCell.check_sound (by decide +kernel) pi_mem reference sigma eta
    shapeK shapeD shapeRoot shapeFactor shapeODE (checks r hr) hx ht
end chebyshev2.Certificates.Compact.ReferenceResiduals
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name,info) in env.constants.toList do
    if (`chebyshev2.Certificates.Compact.ReferenceResiduals).isPrefixOf (Lean.privateToUserName name) then
      if info.isUnsafe then throwError "unsafe residual declaration: {name}"
      for ax in ← Lean.collectAxioms name do
        unless [``propext,``Classical.choice,``Quot.sound].contains ax do
          throwError "forbidden residual axiom: {name}: {ax}"
