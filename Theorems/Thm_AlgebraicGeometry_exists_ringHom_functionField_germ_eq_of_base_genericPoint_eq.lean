import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (hf : f.base (genericPoint Y) = genericPoint X) :
    ∃ δ : ↑X.functionField →+* ↑Y.functionField,
      ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ f ⁻¹ᵁ U)
        (sec : X.presheaf.obj (Opposite.op U)),
        δ ((X.presheaf.germ U (genericPoint X) hU).hom sec) =
          (Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hU').hom ((f.app U).hom sec) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq.solution
