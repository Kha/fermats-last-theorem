import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    [Module.Finite R A] [Module.Free R A]

    (M : Type v) [CommRing M] [HopfAlgebra R M] [Coalgebra.IsCocomm R M] [Module.Free R M] [Module.Finite R M]
    (π : A →ₐc[R] M) (hMet : Algebra.Etale R (CartierDual R M))

    (f : A →ₐ[R] R) (g : M →ₐ[R] R) (hf : f = g.comp (π : A →ₐ[R] M))
    (ψ : CartierDual R A →ₐ[R] R)
    (hψ : ∀ lam : CartierDual R A, ψ lam - lam 1 ∈ IsLocalRing.maximalIdeal R) :
    ψ ((CartierDual.ofDual R A) f.toLinearMap) = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing.solution
