import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_FreyPackage_frey_isSemistableModel

open WeierstrassCurve
theorem FreyPackage.frey_isSemistableModel (P : FreyPackage) : P.freyCurveInt.IsSemistableModel := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_frey_isSemistableModel.solution
