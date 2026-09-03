import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup

open NumberField
theorem NumberField.AdeleRing.compactSpace_quotient_principalSubgroup
    (F : Type) [Field F] [NumberField F] :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup.solution
