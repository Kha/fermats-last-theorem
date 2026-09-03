import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi

open scoped TensorProduct

universe u
theorem Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin (Module.finrank R B) → R')) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi.solution
