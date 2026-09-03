import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_orderedAffineCover_basicOpen_forall_lift_comp_eq_of_isAffine_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_orderedAffineCover_basicOpen_forall_lift_comp_eq_of_isAffine_of_isNilpotent
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} [IsAffine P] (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) [Smooth f] (μ : P₀ ⟶ A)
    (hμ : μ ≫ f = p₀ ≫ Spec.map (CommRingCat.ofHom π)) :
    ∃ (𝒲 : P.OrderedAffineCover) (a : 𝒲.ι → Γ(P, ⊤)) (_ : ∀ i : 𝒲.ι, 𝒲.U i = P.basicOpen (a i))
      (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A),
      (∀ i, m i ≫ f = (𝒲.U i).ι ≫ p) ∧ (∀ i, G ∣_ (𝒲.U i) ≫ m i = (G ⁻¹ᵁ (𝒲.U i)).ι ≫ μ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_orderedAffineCover_basicOpen_forall_lift_comp_eq_of_isAffine_of_isNilpotent.solution
