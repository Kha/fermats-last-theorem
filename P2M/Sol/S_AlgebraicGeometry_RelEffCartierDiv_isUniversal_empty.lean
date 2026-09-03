import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.IdealSheafData.comap_top Scheme.IdealSheafData RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "empty empty_I I_eq_top_of_degree_zero ext I IsUniversal"
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

theorem isUniversal_empty_aux {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal := by
  intro T g D
  refine ⟨⟨g, Category.comp_id g⟩, ?_, ?_⟩
  · change (RelEffCartierDiv.empty f (𝟙 S)).I.comap _ = D.I
    rw [RelEffCartierDiv.empty_I, Scheme.IdealSheafData.comap_top, D.I_eq_top_of_degree_zero]
  · rintro ⟨ψ, hψ⟩ -
    exact Subtype.ext ((Category.comp_id ψ).symm.trans hψ)

end AlgebraicGeometry.RelEffCartierDiv

theorem solution {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal :=
  AlgebraicGeometry.RelEffCartierDiv.isUniversal_empty_aux f
