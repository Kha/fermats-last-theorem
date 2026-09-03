import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq

open scoped TensorProduct

universe u
theorem Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
    (R : Type u) [CommRing R] (B : Type u) [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.Etale R B]
    (n : ℕ) (hn : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) B p = n) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin n → R')) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.solution
