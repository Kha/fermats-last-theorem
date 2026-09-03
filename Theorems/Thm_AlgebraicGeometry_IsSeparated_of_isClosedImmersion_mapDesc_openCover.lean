import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsSeparated.of_isClosedImmersion_mapDesc_openCover
    {N S : Scheme.{u}} (g : N ⟶ S) (𝒰 : Scheme.OpenCover.{u} N)
    (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
    IsSeparated g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover.solution
