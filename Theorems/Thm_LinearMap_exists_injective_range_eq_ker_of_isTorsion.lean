import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_injective_range_eq_ker_of_isTorsion

universe u v

theorem LinearMap.exists_injective_range_eq_ker_of_isTorsion
    {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {D : Type v} [AddCommGroup D] [Module A D] (hD : Module.IsTorsion A D)
    {r : ℕ} (π : (Fin r → A) →ₗ[A] D) :
    ∃ φ : (Fin r → A) →ₗ[A] (Fin r → A),
      Function.Injective φ ∧ LinearMap.range φ = LinearMap.ker π := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_injective_range_eq_ker_of_isTorsion.solution
