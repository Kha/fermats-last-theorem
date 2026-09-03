import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_le_monoidalV2
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.zeroSchemeIdeal Scheme.Modules.zeroSchemeIdeal_comp_le_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules Modules.zeroSchemeIdeal Modules.zeroSchemeIdeal_comp_le_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "zeroSchemeIdeal zeroSchemeIdeal_comp_le_monoidalV2" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
alias AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_comp_le := AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_comp_le_monoidalV2

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2.AlgebraicGeometry"

theorem solution
    {X : Scheme.{u}} {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') [IsIso f] :
    Scheme.Modules.zeroSchemeIdeal (s ≫ f) = Scheme.Modules.zeroSchemeIdeal s := by
  refine le_antisymm (Scheme.Modules.zeroSchemeIdeal_comp_le s f) ?_
  have h := Scheme.Modules.zeroSchemeIdeal_comp_le (s ≫ f) (inv f)
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
