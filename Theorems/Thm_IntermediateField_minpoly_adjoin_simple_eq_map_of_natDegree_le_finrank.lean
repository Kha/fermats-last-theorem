import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_minpoly_adjoin_simple_eq_map_of_natDegree_le_finrank
set_option autoImplicit false

theorem IntermediateField.minpoly_adjoin_simple_eq_map_of_natDegree_le_finrank
    {L F : Type*} [Field L] [Field F] [Algebra L F]
    (x y : F) (P : Polynomial (Polynomial ℤ)) (hP : P.Monic)
    (hxy : P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom F) x) y = 0)
    (hdeg : P.natDegree ≤ Module.finrank (↥(IntermediateField.adjoin L ({x} : Set F)))
      (↥(IntermediateField.adjoin (↥(IntermediateField.adjoin L ({x} : Set F))) ({y} : Set F)))) :
    minpoly (↥(IntermediateField.adjoin L ({x} : Set F))) y =
      P.map (Polynomial.eval₂RingHom (Int.castRingHom (↥(IntermediateField.adjoin L ({x} : Set F))))
        ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_minpoly_adjoin_simple_eq_map_of_natDegree_le_finrank.solution
