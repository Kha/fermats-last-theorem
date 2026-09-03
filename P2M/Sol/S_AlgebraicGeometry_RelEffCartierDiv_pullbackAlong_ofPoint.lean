import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.Hom Scheme Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsSeparated Scheme.IdealSheafData graphOver graphOver_snd RelEffCartierDiv.ofPoint RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver isPullback_mapOnProdOver"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "ofPoint ext pullbackAlong"
namespace OfPointNaturality
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.AlgebraicGeometry.RelEffCartierDiv"

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}

theorem isPullback_graphOver_comp [IsSeparated f] (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ])) φ
      (mapOnProdOver f φ hφ) (graphOver f a ha) := by
  have s : IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) ≫ pullback.snd f g)
      φ φ (graphOver f a ha ≫ pullback.snd f g') := by
    rw [graphOver_snd, graphOver_snd]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine IsPullback.of_right s ?_ (isPullback_mapOnProdOver f φ hφ).flip
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.RelEffCartierDiv.OfPointNaturality

theorem solution {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (RelEffCartierDiv.ofPoint f a ha).pullbackAlong φ hφ =
      RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) := by
  refine RelEffCartierDiv.ext ?_
  change (graphOver f a ha).ker.comap (mapOnProdOver f φ hφ) = (graphOver f (φ ≫ a) _).ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (AlgebraicGeometry.RelEffCartierDiv.OfPointNaturality.isPullback_graphOver_comp
      f a ha φ hφ).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
