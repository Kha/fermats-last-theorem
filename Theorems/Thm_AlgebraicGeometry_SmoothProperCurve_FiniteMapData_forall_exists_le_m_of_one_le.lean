import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_forall_exists_le_m_of_one_le

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.forall_exists_le_m_of_one_le
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (𝔉 : SmoothProperCurve.FiniteMapData c ε) (h𝔉 : 1 ≤ 𝔉.m) (m₀ : ℕ) :
    ∃ 𝔉' : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉'.m ∧ 𝔉'.U = 𝔉.U ∧ 𝔉'.V = 𝔉.V := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_forall_exists_le_m_of_one_le.solution
