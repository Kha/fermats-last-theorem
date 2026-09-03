import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_finiteIndex_principalIdeles_sup_unitIdelesOutside

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

theorem NumberField.AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).FiniteIndex := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_finiteIndex_principalIdeles_sup_unitIdelesOutside.solution
