import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_finiteDimensional_coind_and_finrank_eq_index_mul

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical TensorProduct

theorem Rep.finiteDimensional_coind_and_finrank_eq_index_mul
    {k : Type} [Field k] {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (N : Rep.{0} k H) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind H.subtype N) ∧
      Module.finrank k (Rep.coind H.subtype N) = H.index * Module.finrank k N := by p2m_exact_reverting @_root_.P2MW.S_Rep_finiteDimensional_coind_and_finrank_eq_index_mul.solution
