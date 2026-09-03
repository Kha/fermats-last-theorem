import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ : H →ₐc[R] H') :
    ∃ (Q : Type v) (_ : CommRing Q) (_ : HopfAlgebra R Q) (_ : Module.Finite R Q) (_ : Module.Flat R Q)
      (π : H →ₐc[R] Q) (ι : Q →ₐc[R] H'),
      Function.Surjective π ∧ Function.Injective ι ∧ ι.comp π = φ ∧
      (∀ x ∈ (φ : H →ₐ[R] H').range, Coalgebra.comul (R := R) x ∈
        Submodule.span R {t : H' ⊗[R] H' |
          ∃ a ∈ (φ : H →ₐ[R] H').range, ∃ b ∈ (φ : H →ₐ[R] H').range, t = a ⊗ₜ[R] b}) ∧
      (∀ x ∈ (φ : H →ₐ[R] H').range, HopfAlgebra.antipode R x ∈ (φ : H →ₐ[R] H').range) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem.solution
