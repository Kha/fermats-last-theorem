import Mathlib
import P2M.Util
import P2M.Sol.S_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard

set_option autoImplicit false

theorem IsGaloisGroup.exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard
    (O A B : Type) [CommRing O] [IsNoetherianRing O] [CommRing A] [CommRing B]
    [Algebra O A] [Algebra O B] [Algebra A B] [IsScalarTower O A B] [Algebra.FiniteType O B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G O B]
    [IsGaloisGroup G A B] [FaithfulSMul A B]
    (hG : IsUnit ((Nat.card G : ℕ) : O)) :
    (∃ r : B →ₗ[A] A, ∀ a : A, r (algebraMap A B a) = a) ∧
    (∀ 𝔞 : Ideal O,
      (∀ a : A, algebraMap A B a ∈ 𝔞.map (algebraMap O B) → a ∈ 𝔞.map (algebraMap O A)) ∧
      (∀ b : B, (∀ g : G, g • b - b ∈ 𝔞.map (algebraMap O B)) →
        ∃ a : A, algebraMap A B a - b ∈ 𝔞.map (algebraMap O B))) ∧
    Module.Finite A B ∧ Algebra.FiniteType O A ∧
    (Module.Flat O B → Module.Flat O A) := by p2m_exact_reverting @_root_.P2MW.S_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard.solution
