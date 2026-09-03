import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g : Spec (CommRingCat.of O) ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {r : ℕ} (E : RelEffCartierDiv f r gT)
    (J : (pullback f g).IdealSheafData) [Flat (J.subschemeι ≫ pullback.snd f g)]
    (hJ : J.comap (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) = E.I) :
    ∃ Ebar : RelEffCartierDiv f r g, Ebar.I = J ∧
      Ebar.pullbackAlong (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ = E := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing.solution
