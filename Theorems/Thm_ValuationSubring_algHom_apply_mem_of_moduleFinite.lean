import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_algHom_apply_mem_of_moduleFinite

set_option autoImplicit false

theorem ValuationSubring.algHom_apply_mem_of_moduleFinite
    {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
    (A : ValuationSubring L) (hR : ∀ r : R, algebraMap R L r ∈ A)
    {H : Type} [CommRing H] [Algebra R H] [Module.Finite R H]
    (f : H →ₐ[R] L) (h : H) : f h ∈ A := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_algHom_apply_mem_of_moduleFinite.solution
