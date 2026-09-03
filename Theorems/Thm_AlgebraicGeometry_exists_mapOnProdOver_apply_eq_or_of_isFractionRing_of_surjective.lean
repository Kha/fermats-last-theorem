import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_mapOnProdOver_apply_eq_or_of_isFractionRing_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_mapOnProdOver_apply_eq_or_of_isFractionRing_of_surjective
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {g : Spec (CommRingCat.of O) ⟶ S}
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {k : Type u} [Field k] (toκ : O →+* k) (hκ : Function.Surjective toκ)
    {gk : Spec (CommRingCat.of k) ⟶ S} (hφ : Spec.map (CommRingCat.ofHom toκ) ≫ g = gk)
    (x : ↥(pullback f g)) :
    (∃ y : ↥(pullback f gT), (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).base y = x) ∨
    (∃ z : ↥(pullback f gk), (mapOnProdOver f (Spec.map (CommRingCat.ofHom toκ)) hφ).base z = x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_mapOnProdOver_apply_eq_or_of_isFractionRing_of_surjective.solution
