import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    (∀ V : X.affineOpens,
        Scheme.Modules.coeffIdeal s V.1 ≤ (Scheme.Modules.zeroSchemeIdeal s).ideal V) ∧
    ∀ (U : X.affineOpens) (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
      (Scheme.Modules.zeroSchemeIdeal s).ideal U = Ideal.span {Scheme.Modules.coeff s U.1 τ.hom} ∧
        (Scheme.Modules.zeroSchemeIdeal s).ideal U = Scheme.Modules.coeffIdeal s U.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2.solution
