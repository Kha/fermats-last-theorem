import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {P' P : Scheme.{u}} (p : P ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    [IsIntegral P] [IsIntegral P'] (π : P' ⟶ P) [IsProper π]
    (W : P.Opens) (hW : (W : Set P).Nonempty) [IsIso (π ∣_ W)]
    (w : P) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1) (hwn : IsIntegrallyClosed (P.presheaf.stalk w)) :
    ∃ w' : P', π.base w' = w ∧ IsIso (π.stalkMap w') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one.solution
