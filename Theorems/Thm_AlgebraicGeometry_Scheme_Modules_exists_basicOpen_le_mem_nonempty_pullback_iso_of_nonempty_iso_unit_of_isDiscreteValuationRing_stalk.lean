import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk
    {X : Scheme.{0}} (t : Γ(X, ⊤)) (ξ : X)
    [IsDomain (X.presheaf.stalk ξ)] [IsDiscreteValuationRing (X.presheaf.stalk ξ)]
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) = Ideal.span {X.presheaf.Γgerm ξ t})
    (L L' : X.Modules) (W : X.Opens) (hξ : ξ ∈ W)
    (hLW : Nonempty ((Scheme.Modules.pullback W.ι).obj L ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (hL'W : Nonempty ((Scheme.Modules.pullback W.ι).obj L' ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (h : Nonempty ((Scheme.Modules.pullback (X.basicOpen t).ι).obj L ≅ (Scheme.Modules.pullback (X.basicOpen t).ι).obj L')) :
    ∃ V : X.Opens, X.basicOpen t ≤ V ∧ ξ ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj L ≅ (Scheme.Modules.pullback V.ι).obj L') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk.solution
