import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpenImmersion_mapOnProdOver_specMap_algebraMap_of_isFractionRing_of_isDiscreteValuationRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isOpenImmersion_mapOnProdOver_specMap_algebraMap_of_isFractionRing_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {g : Spec (CommRingCat.of O) ⟶ S}
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT) :
    IsOpenImmersion (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpenImmersion_mapOnProdOver_specMap_algebraMap_of_isFractionRing_of_isDiscreteValuationRing.solution
