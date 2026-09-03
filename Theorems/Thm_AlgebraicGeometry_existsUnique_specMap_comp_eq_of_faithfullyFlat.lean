import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B'] [Module.FaithfullyFlat B B']
    {T : Scheme.{u}} (φ' : Spec (CommRingCat.of B') ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[B] B')) ≫ φ' =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B' →ₐ[B] B' ⊗[B] B').toRingHom) ≫ φ') :
    ∃! φ : Spec (CommRingCat.of B) ⟶ T, Spec.map (CommRingCat.ofHom (algebraMap B B')) ≫ φ = φ' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat.solution
