import Mathlib
import P2M.Util
import P2M.Sol.S_BialgHom_exists_comp_eq_comp_of_surjective_of_ker_le

set_option autoImplicit false

universe u v

theorem BialgHom.exists_comp_eq_comp_of_surjective_of_ker_le
    {R : Type u} [CommRing R]
    {H₁ H₂ H₁' H₂' : Type v} [CommRing H₁] [Bialgebra R H₁] [CommRing H₂] [Bialgebra R H₂]
    [CommRing H₁'] [Bialgebra R H₁'] [CommRing H₂'] [Bialgebra R H₂']
    (π₁ : H₁ →ₐc[R] H₁') (π₂ : H₂ →ₐc[R] H₂') (hπ₂ : Function.Surjective π₂)
    (r : H₂ →ₐc[R] H₁) (hker : ∀ x : H₂, π₂ x = 0 → π₁ (r x) = 0) :
    ∃ r' : H₂' →ₐc[R] H₁', r'.comp π₂ = π₁.comp r ∧
      (Function.Surjective π₁ → Function.Surjective r → Function.Surjective r') := by p2m_exact_reverting @_root_.P2MW.S_BialgHom_exists_comp_eq_comp_of_surjective_of_ker_le.solution
