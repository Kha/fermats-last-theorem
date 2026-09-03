import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one
    {k : Type u} [Field k] [IsAlgClosed k] {T Y : Scheme.{u}}
    (fT : T ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fT] [QuasiCompact fT] [LocallyOfFiniteType fY] [QuasiCompact fY]
    (u : T ⟶ Y) (hu : u ≫ fY = fT)
    [IrreducibleSpace ↑Y] (hdim : topologicalKrullDim ↑Y ≤ 1)
    (hinj : ∀ x₁ x₂ : Spec (CommRingCat.of k) ⟶ T, x₁ ≫ fT = 𝟙 _ → x₂ ≫ fT = 𝟙 _ → x₁ ≫ u = x₂ ≫ u → x₁ = x₂)
    (hsurj : ∀ y : Spec (CommRingCat.of k) ⟶ Y, y ≫ fY = 𝟙 _ → ∃ x : Spec (CommRingCat.of k) ⟶ T, x ≫ fT = 𝟙 _ ∧ x ≫ u = y)
    (hT : ∀ c : ↑T, IsClopen ({c} : Set ↑T) → Finite ↑T) :
    IrreducibleSpace ↑T := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one.solution
