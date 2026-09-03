import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_etale_opensInclusion_comp_of_formallyUnramified_stalkMap_of_smoothOfRelativeDimension

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_etale_opensInclusion_comp_of_formallyUnramified_stalkMap_of_smoothOfRelativeDimension
    {k : Type u} [Field k] {X Y : Scheme.{u}} (n : ℕ)
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension n fY]
    (φ : X ⟶ Y) (hφ : φ ≫ fY = fX) (x : X) (hx : (φ.stalkMap x).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ φ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_etale_opensInclusion_comp_of_formallyUnramified_stalkMap_of_smoothOfRelativeDimension.solution
