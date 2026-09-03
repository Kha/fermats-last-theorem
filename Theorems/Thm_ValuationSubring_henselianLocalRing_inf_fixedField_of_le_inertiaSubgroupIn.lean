import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn

set_option autoImplicit false

universe u

theorem ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.solution
