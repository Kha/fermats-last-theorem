import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit
    {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    {B C H : Type*} [CommRing B] [CommRing C] [CommRing H] [Bialgebra R B] [Bialgebra R C] [Bialgebra R H]
    (ψ : B →ₐc[R] C) (q : C →ₐc[R] H) (hq : Function.Surjective q)
    (hkerq : RingHom.ker (q : C →+* H) = Ideal.map (ψ : B →ₐ[R] C) (RingHom.ker (Bialgebra.counitAlgHom R B)))
    {T : Type*} [CommRing T] [Bialgebra S T]
    (π : S ⊗[R] C →ₐc[S] T) (hπ : Function.Surjective π)
    (hkerπ : RingHom.ker (π : S ⊗[R] C →ₐ[S] T) =
      Ideal.map (Bialgebra.TensorProduct.map (BialgHom.id S S) ψ : S ⊗[R] B →ₐ[S] S ⊗[R] C)
        (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] B)))) :
    ∃ e : T ≃ₐc[S] S ⊗[R] H, ∀ x : S ⊗[R] C, e (π x) = Bialgebra.TensorProduct.map (BialgHom.id S S) q x := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit.solution
