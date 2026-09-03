import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn

set_option autoImplicit false

universe u

open IsLocalRing

theorem ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L) :
    HenselianLocalRing ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn K)) L)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn.solution
