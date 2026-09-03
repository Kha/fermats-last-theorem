import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_surjective_ker_eq_span_one_sub_of_counit_eq_one_of_isLocalRing_quotient

set_option autoImplicit false

universe u v

open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_surjective_ker_eq_span_one_sub_of_counit_eq_one_of_isLocalRing_quotient
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    (e₀ : H) (he₀ : IsIdempotentElem e₀) (hε : Coalgebra.counit (R := R) e₀ = 1)
    (hloc : IsLocalRing (H ⧸ Ideal.span {1 - e₀})) :
    ∃ (H₀ : Type v) (_ : CommRing H₀) (_ : HopfAlgebra R H₀) (π : H →ₐc[R] H₀),
      Function.Surjective π ∧ RingHom.ker (π : H →ₐ[R] H₀) = Ideal.span {1 - e₀} ∧
      IsLocalRing H₀ ∧ Module.Finite R H₀ ∧
      (Coalgebra.IsCocomm R H → Coalgebra.IsCocomm R H₀) ∧ (Module.Flat R H → Module.Flat R H₀) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_surjective_ker_eq_span_one_sub_of_counit_eq_one_of_isLocalRing_quotient.solution
