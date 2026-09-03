import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_away_forall_nonempty_basis_tensorProduct_of_projective_of_finite

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem Module.exists_away_forall_nonempty_basis_tensorProduct_of_projective_of_finite
    {S : Type u} [CommRing S] (P : Type u) [AddCommGroup P] [Module S P] [Module.Finite S P] [Module.Projective S P]
    (p : PrimeSpectrum S) :
    ∃ r : S, r ∉ p.asIdeal ∧
      ∀ (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization.Away r S'],
        ∃ m : ℕ, Nonempty (Module.Basis (Fin m) S' (S' ⊗[S] P)) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_away_forall_nonempty_basis_tensorProduct_of_projective_of_finite.solution
