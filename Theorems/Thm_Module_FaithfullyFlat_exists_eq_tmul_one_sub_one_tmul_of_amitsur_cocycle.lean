import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle

set_option autoImplicit false

universe u v

open TensorProduct

theorem Module.FaithfullyFlat.exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (c : S ⊗[R] S)
    (hc : Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) c +
          (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) c =
        Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) c) :
    ∃ s : S, c = s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle.solution
