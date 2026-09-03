import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_surjective_bialgHom_ker_eq_map_ker

set_option autoImplicit false

universe u v w x

theorem Bialgebra.exists_surjective_bialgHom_ker_eq_map_ker
    (k : Type u) [Field k]
    {A : Type v} [CommRing A] [Bialgebra k A]
    {B : Type w} [CommRing B] [Bialgebra k B]
    {C : Type x} [CommRing C] [Bialgebra k C]
    (π : A →ₐc[k] B) (μ : A →ₐc[k] C)
    (hπ : Function.Surjective π) (hμ : Function.Surjective μ) :
    ∃ (D : Type w) (_ : CommRing D) (_ : Bialgebra k D) (ρ : B →ₐc[k] D),
      Function.Surjective ρ ∧
      RingHom.ker (ρ : B →ₐ[k] D) = Ideal.map (π : A →ₐ[k] B) (RingHom.ker (μ : A →ₐ[k] C)) := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_surjective_bialgHom_ker_eq_map_ker.solution
