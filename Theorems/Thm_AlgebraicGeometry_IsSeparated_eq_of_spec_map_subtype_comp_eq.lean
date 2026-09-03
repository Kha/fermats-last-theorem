import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq
set_option Elab.async false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsSeparated.eq_of_spec_map_subtype_comp_eq
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f]
    {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    (s₁ s₂ : Spec (CommRingCat.of ↥A) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom A.subtype) ≫ s₁ = Spec.map (CommRingCat.ofHom A.subtype) ≫ s₂)
    (hf : s₁ ≫ f = s₂ ≫ f) : s₁ = s₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq.solution
