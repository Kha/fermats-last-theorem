import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    {X X₀ : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of Ω)} {f₀ : X₀ ⟶ Spec (CommRingCat.of F)} (r : X ⟶ X₀)
    (hr : IsPullback r fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))) :
    Surjective r ∧ Flat r ∧ QuasiCompact r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field.solution
