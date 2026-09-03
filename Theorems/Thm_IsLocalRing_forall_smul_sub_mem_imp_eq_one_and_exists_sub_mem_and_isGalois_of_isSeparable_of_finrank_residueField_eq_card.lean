import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_forall_smul_sub_mem_imp_eq_one_and_exists_sub_mem_and_isGalois_of_isSeparable_of_finrank_residueField_eq_card

set_option autoImplicit false

theorem IsLocalRing.forall_smul_sub_mem_imp_eq_one_and_exists_sub_mem_and_isGalois_of_isSeparable_of_finrank_residueField_eq_card
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (hres : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) (IsLocalRing.residue A a) =
      IsLocalRing.residue B (algebraMap A B a))
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    (hf : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) = Nat.card G) :
    (∀ g : G, (∀ b : B, g • b - b ∈ IsLocalRing.maximalIdeal B) → g = 1) ∧
    (∀ b : B, (∀ g : G, g • b - b ∈ IsLocalRing.maximalIdeal B) → ∃ a : A, b - algebraMap A B a ∈ IsLocalRing.maximalIdeal B) ∧
    IsGalois (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_forall_smul_sub_mem_imp_eq_one_and_exists_sub_mem_and_isGalois_of_isSeparable_of_finrank_residueField_eq_card.solution
