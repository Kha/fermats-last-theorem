import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_comp_eq_of_injective_baseChange_of_finrank_eq_of_comp_eq_counit

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_comp_eq_of_injective_baseChange_of_finrank_eq_of_comp_eq_counit
    {O : Type} [CommRing O]
    {B C K : Type} [CommRing B] [CommRing C] [CommRing K] [HopfAlgebra O B] [HopfAlgebra O C] [HopfAlgebra O K]
    [Module.Finite O B] [Module.Free O B] [Module.Finite O C] [Module.Free O C] [Module.Finite O K] [Module.Free O K]
    (ψ : B →ₐc[O] C)
    (q : C →ₐc[O] K) (hq : Function.Surjective q)
    (hkerq : RingHom.ker (q : C →+* K) = Ideal.map (ψ : B →ₐ[O] C) (RingHom.ker (Bialgebra.counitAlgHom O B)))

    (hrk : Module.finrank O B * Module.finrank O K = Module.finrank O C)
    (k : Type) [Field k] [Algebra O k]
    {A : Type} [CommRing A] [Bialgebra k A]

    (hψk : Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id k k) ψ))
    (f : A →ₐc[k] k ⊗[O] C)
    (hf : ((Bialgebra.TensorProduct.map (BialgHom.id k k) q).comp f : A →ₐ[k] k ⊗[O] K) =
      (Algebra.ofId k (k ⊗[O] K)).comp (Bialgebra.counitAlgHom k A)) :
    ∃ g : A →ₐc[k] k ⊗[O] B, (Bialgebra.TensorProduct.map (BialgHom.id k k) ψ).comp g = f := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_comp_eq_of_injective_baseChange_of_finrank_eq_of_comp_eq_counit.solution
