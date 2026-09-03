import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    {Y : Scheme.{u}} (φ' : T' ⟶ Y) (hφ' : q₁ ≫ φ' = q₂ ≫ φ') :
    ∃! φ : T ⟶ Y, p ≫ φ = φ' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat.solution
