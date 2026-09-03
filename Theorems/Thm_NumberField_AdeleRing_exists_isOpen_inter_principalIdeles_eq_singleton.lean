import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton
    (F : Type) [Field F] [NumberField F] :
    ∃ V : Set (AdeleRing (𝓞 F) F)ˣ, IsOpen V ∧
      V ∩ (M4aHerbrand.principalIdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F)ˣ) = {1} := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton.solution
