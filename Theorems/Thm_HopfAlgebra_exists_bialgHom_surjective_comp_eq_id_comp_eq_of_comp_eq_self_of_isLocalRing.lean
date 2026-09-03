import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing
    (R : Type) [CommRing R] [IsLocalRing R]
    (A : Type) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    [Module.Finite R A] [Module.Free R A]
    (ε : A →ₐc[R] A) (hε : ε.comp ε = ε) :
    ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra R C) (_ : Coalgebra.IsCocomm R C)
      (_ : Module.Finite R C) (_ : Module.Free R C)
      (q : A →ₐc[R] C) (i : C →ₐc[R] A),
      Function.Surjective q ∧ q.comp i = BialgHom.id R C ∧ i.comp q = ε := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing.solution
