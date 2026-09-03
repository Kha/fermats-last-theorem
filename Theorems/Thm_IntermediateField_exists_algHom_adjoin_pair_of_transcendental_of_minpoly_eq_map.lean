import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_algHom_adjoin_pair_of_transcendental_of_minpoly_eq_map
set_option autoImplicit false

theorem IntermediateField.exists_algHom_adjoin_pair_of_transcendental_of_minpoly_eq_map
    {L F A : Type*} [Field L] [Field F] [Field A] [Algebra L F] [Algebra L A]
    (x y : F) (hx : Transcendental L x) (P : Polynomial (Polynomial ℤ)) (hP : P.Monic)
    (hmin : minpoly (↥(IntermediateField.adjoin L ({x} : Set F))) y =
      P.map (Polynomial.eval₂RingHom (Int.castRingHom (↥(IntermediateField.adjoin L ({x} : Set F))))
        ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩))
    (c z : A) (hc : Transcendental L c)
    (hz : (P.map (Polynomial.eval₂RingHom (Int.castRingHom A) c)).IsRoot z) :
    ∃ ψ : ↥(IntermediateField.adjoin L ({x, y} : Set F)) →ₐ[L] A,
      ψ ⟨x, IntermediateField.subset_adjoin L _ (Set.mem_insert x {y})⟩ = c ∧
      ψ ⟨y, IntermediateField.subset_adjoin L _ (Set.mem_insert_of_mem x rfl)⟩ = z := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_algHom_adjoin_pair_of_transcendental_of_minpoly_eq_map.solution
