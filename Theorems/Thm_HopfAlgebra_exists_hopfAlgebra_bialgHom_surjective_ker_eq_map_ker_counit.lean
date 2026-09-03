import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit

universe u v w

theorem HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] (φ : A →ₐc[R] B) :
    ∃ (H : Type w) (_ : CommRing H) (_ : HopfAlgebra R H) (q : B →ₐc[R] H),
      Function.Surjective q ∧
      RingHom.ker (q : B →+* H) =
        Ideal.map (φ : A →ₐ[R] B) (RingHom.ker (Bialgebra.counitAlgHom R A)) ∧
      (Coalgebra.IsCocomm R B → Coalgebra.IsCocomm R H) ∧
      (Module.Finite R B → Module.Finite R H) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit.solution
