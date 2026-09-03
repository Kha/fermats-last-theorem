import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_counit_finitePartIdempotent

open scoped TensorProduct

theorem HopfAlgebra.counit_finitePartIdempotent
    (R : Type*) [CommRing R] [IsLocalRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e)
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤) :
    Coalgebra.counit (R := R) e = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_counit_finitePartIdempotent.solution
