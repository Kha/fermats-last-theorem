import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback
    {κ k : Type u} [Field κ] [Field k] [Algebra κ k]
    {X S : Scheme.{u}} (f : X ⟶ S) (a : Spec (CommRingCat.of κ) ⟶ S) (b : Spec (CommRingCat.of k) ⟶ S)
    (hb : b = Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ a)

    (Z₀ Z₁ : Set ↥(pullback f a))
    (hZ₀ : Z₀ ∈ irreducibleComponents ↥(pullback f a)) (hZ₁ : Z₁ ∈ irreducibleComponents ↥(pullback f a))
    (hne : Z₀ ≠ Z₁) (hall : ∀ Z ∈ irreducibleComponents ↥(pullback f a), Z = Z₀ ∨ Z = Z₁)

    [IsReduced (pullback f b)]
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ pullback f b) [IsClosedImmersion i]
    (F : Set ↥(pullback f b)) (hF : IsIrreducible F) (hFc : IsClosed F)
    (hcover : ∀ z : ↥(pullback f b), z ∈ Set.range i.base ∨ z ∈ F) :
    ∃ (Cₚ : Scheme.{u}) (iₚ : Cₚ ⟶ pullback f a) (g : C ⟶ Cₚ),
      IsClosedImmersion iₚ ∧ IsIntegral Cₚ ∧
      Set.range iₚ.base ∈ irreducibleComponents ↥(pullback f a) ∧
      IsPullback g (i ≫ pullback.snd f b) (iₚ ≫ pullback.snd f a) (Spec.map (CommRingCat.ofHom (algebraMap κ k))) ∧
      g ≫ iₚ ≫ pullback.fst f a = i ≫ pullback.fst f b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback.solution
