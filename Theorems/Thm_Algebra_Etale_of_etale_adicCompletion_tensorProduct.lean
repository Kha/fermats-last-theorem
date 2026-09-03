import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_of_etale_adicCompletion_tensorProduct

set_option autoImplicit false

universe u v

open scoped TensorProduct in

theorem Algebra.Etale.of_etale_adicCompletion_tensorProduct
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (h : Algebra.Etale (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      ((AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗[R] S)) :
    Algebra.Etale R S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_of_etale_adicCompletion_tensorProduct.solution
