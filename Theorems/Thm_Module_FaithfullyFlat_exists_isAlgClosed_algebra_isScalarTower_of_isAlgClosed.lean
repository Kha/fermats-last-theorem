import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed

set_option autoImplicit false

theorem Module.FaithfullyFlat.exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed
    (R W k : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
    [Field k] [IsAlgClosed k] [Algebra R k] :
    ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (_ : Algebra R k') (_ : Algebra W k') (_ : Algebra k k'),
      IsScalarTower R W k' ∧ IsScalarTower R k k' := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_isAlgClosed_algebra_isScalarTower_of_isAlgClosed.solution
