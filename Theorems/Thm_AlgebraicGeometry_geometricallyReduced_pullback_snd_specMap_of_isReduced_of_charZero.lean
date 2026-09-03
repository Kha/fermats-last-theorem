import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero
    (𝒪₀ : Type u) [CommRing 𝒪₀] [IsDomain 𝒪₀] [CharZero 𝒪₀]
    (K₀ : Type u) [Field K₀] [Algebra 𝒪₀ K₀] [IsFractionRing 𝒪₀ K₀]
    (𝒳₀ : Scheme.{u}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀)) [IsReduced 𝒳₀] [LocallyOfFiniteType f₀] :
    GeometricallyReduced (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪₀ K₀)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero.solution
