import nesterov.Oracle.GeometricData
import nesterov.Oracle.ExtensionData

namespace nesterov.Oracle.Geometric
noncomputable section

def data (N : ℕ) (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    ExtensionData (Fin (N+2)) (ChainSpace N) where
  q := s^2
  q_pos := sq_pos_of_pos hs
  q_lt_one := by nlinarith
  slopes := fun i=>slope N s i.val
  offsets := fun i=>offset N s i.val


end
end nesterov.Oracle.Geometric
