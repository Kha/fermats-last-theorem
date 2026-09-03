import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K' : Subalgebra k H)
    (hΔ' : ∀ x ∈ K', Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b})
    (hS' : ∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') :
    ∃ (Hb : Type v) (_ : CommRing Hb) (_ : HopfAlgebra k Hb) (π : H →ₐc[k] Hb),
      Function.Surjective π ∧
      RingHom.ker (π : H →+* Hb) = Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0} ∧
      (∀ x : H, Coalgebra.counit (R := k) (π x) = Coalgebra.counit (R := k) x) ∧
      (∀ x : H, π (HopfAlgebra.antipode k x) = HopfAlgebra.antipode k (π x)) ∧
      ∀ (K : Subalgebra k H),
        (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
          Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
        (∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) →
        (∀ y ∈ K.map (π : H →ₐ[k] Hb), Coalgebra.comul (R := k) y ∈
          Submodule.span k {t : Hb ⊗[k] Hb |
            ∃ a ∈ K.map (π : H →ₐ[k] Hb), ∃ b ∈ K.map (π : H →ₐ[k] Hb), t = a ⊗ₜ[k] b}) ∧
        (∀ y ∈ K.map (π : H →ₐ[k] Hb), HopfAlgebra.antipode k y ∈ K.map (π : H →ₐ[k] Hb)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem.solution
