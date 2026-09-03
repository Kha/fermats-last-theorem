import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.IsStandardEtale.exists_isStandardEtale_tensorProduct_algEquiv_of_surjective
    {C C₀ : Type} [CommRing C] [CommRing C₀] [Algebra C C₀] (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧ Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective.solution
