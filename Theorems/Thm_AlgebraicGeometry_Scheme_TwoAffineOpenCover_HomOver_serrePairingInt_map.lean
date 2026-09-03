import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_serrePairingInt_map

universe u w

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.serrePairingInt_map
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] {τ : R →+* S}
    {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
    {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)} {ι : Type w} [Fintype ι]
    (f : Scheme.TwoAffineOpenCover.HomOver τ 𝒱 c 𝒲 c')
    (Λ : ι → (𝒱.cover c).LaurentChart) (Λ' : ι → (𝒲.cover c').LaurentChart)
    (hΛ : ∀ i y, (Λ' i).expand (f.map01 y) = ((Λ i).expand y).map τ)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ) (hv' : (𝒲.cover c').ResiduesVanishOnCoboundaries Λ')
    (ω : (𝒱.kaehlerSections c).H0) (x : (𝒱.structureSheafSections c).H1) :
    (𝒲.cover c').serrePairingInt Λ' hv' (f.kaehlerH0map ω) (f.H1map x) =
      τ ((𝒱.cover c).serrePairingInt Λ hv ω x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_serrePairingInt_map.solution
