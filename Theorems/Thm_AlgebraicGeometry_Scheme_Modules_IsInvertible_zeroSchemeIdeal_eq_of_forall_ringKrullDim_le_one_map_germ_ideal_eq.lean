import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (s : 𝟙_ X.Modules ⟶ M) (s' : 𝟙_ X.Modules ⟶ M') (hs : s ≠ 0)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → ∀ (U : X.affineOpens) (hxU : x ∈ (U : X.Opens)),
      Ideal.map (X.presheaf.germ U x hxU).hom ((Scheme.Modules.zeroSchemeIdeal s).ideal U) =
        Ideal.map (X.presheaf.germ U x hxU).hom ((Scheme.Modules.zeroSchemeIdeal s').ideal U)) :
    Scheme.Modules.zeroSchemeIdeal s = Scheme.Modules.zeroSchemeIdeal s' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_forall_ringKrullDim_le_one_map_germ_ideal_eq.solution
