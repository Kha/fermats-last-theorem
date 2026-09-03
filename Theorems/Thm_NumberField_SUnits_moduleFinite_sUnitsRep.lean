import Mathlib
import Definitions.Def_NumberField_SUnitsModule
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_moduleFinite_sUnitsRep

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem NumberField.SUnits.moduleFinite_sUnitsRep (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) : Module.Finite ℤ (NumberField.SUnits.sUnitsRep E K S) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_moduleFinite_sUnitsRep.solution
