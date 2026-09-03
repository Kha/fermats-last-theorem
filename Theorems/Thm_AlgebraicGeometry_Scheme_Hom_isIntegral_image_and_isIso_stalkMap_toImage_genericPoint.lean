import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Hom.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
    {X P : Scheme.{u}} [IsIntegral X] (f : X ⟶ P) [IsImmersion f] [QuasiCompact f] :
    ∃ (_ : IsIntegral f.image),
      f.toImage.base (genericPoint X) = genericPoint f.image ∧
      IsIso (f.toImage.stalkMap (genericPoint X)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint.solution
