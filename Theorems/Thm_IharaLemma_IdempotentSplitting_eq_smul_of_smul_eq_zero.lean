import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.eq_smul_of_smul_eq_zero {B : Type} [CommRing B]
    (S : IharaLemma.IdempotentSplitting B) {M : Type} [AddCommGroup M] [Module B M]
    {u : B} {y : M} (huy : u • y = 0) (i₀ : Fin S.n) (hu : ∀ j, j ≠ i₀ → u ∉ S.𝔪 j) :
    y = S.e i₀ • y := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero.solution
