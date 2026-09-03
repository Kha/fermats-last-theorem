import Mathlib
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_IdempotentSplitting_mem_maxIdeal_iff_apply_toCornerRing_eq_zero

set_option autoImplicit false

open IharaLemma

theorem IharaLemma.IdempotentSplitting.mem_maxIdeal_iff_apply_toCornerRing_eq_zero
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Sp : IdempotentSplitting B) (i : Fin Sp.n)
    (π : Sp.CornerRing i →ₐ[𝒪] IsLocalRing.ResidueField 𝒪) (x : B) :
    x ∈ Sp.𝔪 i ↔ π (Sp.toCornerRing i x) = 0 := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_IdempotentSplitting_mem_maxIdeal_iff_apply_toCornerRing_eq_zero.solution
