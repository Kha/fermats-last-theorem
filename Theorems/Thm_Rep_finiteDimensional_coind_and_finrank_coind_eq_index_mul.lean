import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul {k G : Type u} [Field k] [Group G] (S : Subgroup G) [S.FiniteIndex]
    (N : Rep.{u} k S) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind S.subtype N) ∧
      Module.finrank k (Rep.coind S.subtype N) = S.index * Module.finrank k N := by p2m_exact_reverting @_root_.P2MW.S_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul.solution
