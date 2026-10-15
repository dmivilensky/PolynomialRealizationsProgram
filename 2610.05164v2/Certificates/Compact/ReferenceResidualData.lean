import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data000
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data001
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data002
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data003
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data004
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data005
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data006
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data007
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data008
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data009
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data010
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data011
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data012
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data013
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data014
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data015
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data016
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data017
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data018
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data019
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data020
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data021
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data022
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data023
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data024
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data025
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data026
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data027
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data028
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data029
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data030
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data031
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data032
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data033
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data034
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data035
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data036
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data037
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data038
import «2610.05164v2».Certificates.Compact.ReferenceResidualBatches.Data039

/-!
Article: 2610.05164v2, Section 4.1.
Reference Residual Data.
Use: `«2610.05164v2».Certificates.Compact.ReferenceResiduals.rows` feeds
`«2610.05164v2».Certificates.Compact.ReferenceTrajectory.full_trajectory` (full trajectory).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace «2610.05164v2».Certificates.Compact.ReferenceResiduals
open «2610.05164v2».Numerics.IntegerCertificate
noncomputable def rows : List ResidualCell.Row := block0++block1++block2++block3++block4++block5++block6++block7++block8++block9++block10++block11++block12++block13++block14++block15++block16++block17++block18++block19++block20++block21++block22++block23++block24++block25++block26++block27++block28++block29++block30++block31++block32++block33++block34++block35++block36++block37++block38++block39++block40++block41++block42++block43++block44++block45++block46++block47++block48++block49++block50++block51++block52++block53++block54++block55++block56++block57++block58++block59++block60++block61++block62++block63++block64++block65++block66++block67++block68++block69++block70++block71++block72++block73++block74++block75++block76++block77++block78++block79++block80++block81++block82++block83++block84++block85++block86++block87++block88++block89++block90++block91++block92++block93++block94++block95++block96++block97++block98++block99++block100++block101++block102++block103++block104++block105++block106++block107++block108++block109++block110++block111++block112++block113++block114++block115++block116++block117++block118++block119++block120++block121++block122++block123++block124++block125++block126++block127++block128++block129++block130++block131++block132++block133++block134++block135++block136++block137++block138++block139++block140++block141++block142++block143++block144++block145++block146++block147++block148++block149++block150++block151++block152++block153++block154++block155++block156++block157
end «2610.05164v2».Certificates.Compact.ReferenceResiduals
