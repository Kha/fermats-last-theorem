import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff

set_option autoImplicit false

open scoped TensorProduct

theorem Module.exists_ideal_forall_projective_and_rankAtStalk_eq_iff
    (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)
    (hr : ∀ p : PrimeSpectrum A,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M) ≤ r) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type) [CommRing B] [Algebra A B],
      (Module.Projective B (B ⊗[A] M) ∧ ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = r) ↔
        ∀ a ∈ 𝔞, algebraMap A B a = 0 := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff.solution
