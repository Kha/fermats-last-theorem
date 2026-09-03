import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_comul_finitePartIdempotent_mul

open scoped TensorProduct

theorem HopfAlgebra.comul_finitePartIdempotent_mul
    (R : Type*) [CommRing R] [IsLocalRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤) :
    Coalgebra.comul (R := R) e * (e ⊗ₜ[R] 1) = e ⊗ₜ[R] e ∧ Coalgebra.comul (R := R) e * (1 ⊗ₜ[R] e) = e ⊗ₜ[R] e := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.solution
