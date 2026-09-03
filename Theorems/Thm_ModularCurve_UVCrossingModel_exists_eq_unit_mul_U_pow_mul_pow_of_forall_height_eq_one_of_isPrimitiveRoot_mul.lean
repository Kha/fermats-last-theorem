import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_pow_of_forall_height_eq_one_of_isPrimitiveRoot_mul

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_eq_unit_mul_U_pow_mul_pow_of_forall_height_eq_one_of_isPrimitiveRoot_mul
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmnW : IsUnit ((m * n : ℕ) : W)) (hμ' : ∃ ζ : W, IsPrimitiveRoot ζ (m * n))
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (f : K₀) (hf : f ≠ 0)
    (hloc : ∀ (P : Ideal (UVCrossingModel W (π ^ (m * n)))) [P.IsPrime], P.height = 1 →
      ∃ (g : K₀) (r s : UVCrossingModel W (π ^ (m * n))), r ∉ P ∧ s ∉ P ∧
        f * algebraMap _ K₀ s = g ^ n * algebraMap _ K₀ r) :
    ∃ (u : (UVCrossingModel W (π ^ (m * n)))ˣ) (j : ℕ) (h : K₀),
      f = algebraMap _ K₀ (u : UVCrossingModel W (π ^ (m * n))) *
        algebraMap _ K₀ (U (π ^ (m * n))) ^ j * h ^ n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_pow_of_forall_height_eq_one_of_isPrimitiveRoot_mul.solution
