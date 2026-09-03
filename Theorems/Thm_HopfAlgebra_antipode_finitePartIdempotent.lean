import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_antipode_finitePartIdempotent

open scoped TensorProduct

theorem HopfAlgebra.antipode_finitePartIdempotent
    (R : Type*) [CommRing R] [IsLocalRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤) :
    HopfAlgebra.antipode R e = e := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_antipode_finitePartIdempotent.solution
