import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.tensorPow
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)} {L : A.Modules}
    (hL : IsAlgEquivZero a L) (n : ℕ) : IsAlgEquivZero a (L.tensorPow n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow.solution
