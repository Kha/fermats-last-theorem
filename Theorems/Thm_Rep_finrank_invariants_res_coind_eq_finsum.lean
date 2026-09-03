import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_finrank_invariants_res_coind_eq_finsum

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical TensorProduct

theorem Rep.finrank_invariants_res_coind_eq_finsum
    {k : Type} [Field k] {G : Type} [Group G] (H D : Subgroup G) [H.FiniteIndex]
    (N : Rep.{0} k H) [FiniteDimensional k N] :
    Module.finrank k (Rep.res D.subtype (Rep.coind H.subtype N)).ρ.invariants =
      ∑ᶠ q : Quotient (MulAction.orbitRel H (G ⧸ D)),
        Module.finrank k (Rep.res (MulAction.stabilizer H q.out).subtype N).ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_Rep_finrank_invariants_res_coind_eq_finsum.solution
