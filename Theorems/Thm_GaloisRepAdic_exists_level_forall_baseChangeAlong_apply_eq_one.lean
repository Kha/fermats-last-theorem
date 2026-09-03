import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one

set_option autoImplicit false

theorem GaloisRepAdic.exists_level_forall_baseChangeAlong_apply_eq_one
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (K : ℕ) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ {B : Type} [CommRing B] [IsLocalRing B] (f : A →+* B) (hf : IsLocalHom f),
        (∀ a ∈ IsLocalRing.maximalIdeal A ^ K, f a = 0) →
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, s x = x) →
          (ρ.baseChangeAlong f hf).ρ s = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one.solution
