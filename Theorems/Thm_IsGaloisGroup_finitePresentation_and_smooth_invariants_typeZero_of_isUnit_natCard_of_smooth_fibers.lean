import Mathlib
import P2M.Util
import P2M.Sol.S_IsGaloisGroup_finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers

set_option autoImplicit false

theorem IsGaloisGroup.finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
    (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O]
    (A B : Type) [CommRing A] [CommRing B] [IsDomain B]
    [Algebra O A] [Algebra O B] [Algebra A B] [IsScalarTower O A B] [Algebra.FiniteType O B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G O B]
    [IsGaloisGroup G A B] [FaithfulSMul A B]
    (hG : IsUnit ((Nat.card G : ℕ) : O)) :

    Algebra.FiniteType O A ∧ Algebra.FinitePresentation O A ∧ Module.Finite A B ∧

    (IsIntegrallyClosed B → IsIntegrallyClosed A) ∧

    (Module.Flat O B → Module.Flat O A) ∧

    (∀ 𝔞 : Ideal O,
      (∀ a : A, algebraMap A B a ∈ 𝔞.map (algebraMap O B) → a ∈ 𝔞.map (algebraMap O A)) ∧
      (∀ b : B, (∀ g : G, g • b - b ∈ 𝔞.map (algebraMap O B)) → ∃ a : A, algebraMap A B a - b ∈ 𝔞.map (algebraMap O B)) ∧
      (∀ n : ℕ, Ring.KrullDimLE n (B ⧸ 𝔞.map (algebraMap O B)) → Ring.KrullDimLE n (A ⧸ 𝔞.map (algebraMap O A)))) ∧

    (Module.Flat O B →
      (∀ (𝔭 : Ideal O) [𝔭.IsPrime], Algebra.FormallySmooth 𝔭.ResidueField (𝔭.Fiber A)) →
      Algebra.Smooth O A) := by p2m_exact_reverting @_root_.P2MW.S_IsGaloisGroup_finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers.solution
