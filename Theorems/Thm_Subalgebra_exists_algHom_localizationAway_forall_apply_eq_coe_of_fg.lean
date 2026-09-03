import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg

set_option autoImplicit false

universe u

theorem Subalgebra.exists_algHom_localizationAway_forall_apply_eq_coe_of_fg
    {R : Type u} [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (T : Subalgebra R (Localization.AtPrime 𝔭)) (hT : T.FG) :
    ∃ (r : R) (_ : r ∉ 𝔭) (ψ : ↥T →ₐ[R] Localization.Away r),
      ∀ (π : Localization.Away r →ₐ[R] Localization.AtPrime 𝔭) (x : ↥T),
        π (ψ x) = (x : Localization.AtPrime 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg.solution
