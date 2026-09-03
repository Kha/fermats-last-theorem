import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_preimage_support_zeroSchemeIdeal_eq_of_forall_pullbackSection_eq_zero_iff_comp

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.preimage_support_zeroSchemeIdeal_eq_of_forall_pullbackSection_eq_zero_iff_comp
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) (T : X ⟶ X)
    (hs : ∀ z : Spec (CommRingCat.of k) ⟶ X, z ≫ f = 𝟙 _ →
      (Scheme.Modules.pullbackSection z s = 0 ↔ Scheme.Modules.pullbackSection (z ≫ T) s = 0)) :
    T.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) =
      ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_preimage_support_zeroSchemeIdeal_eq_of_forall_pullbackSection_eq_zero_iff_comp.solution
