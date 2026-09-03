import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.isCompact_setOf_sq_mem_of_isCompact
    (K : Type) [Field K] [NumberField K]
    (C : Set (AdeleRing (𝓞 K) K)ˣ) (hC : IsCompact C) :
    IsCompact {u : (AdeleRing (𝓞 K) K)ˣ | u ^ 2 ∈ C} := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact.solution
