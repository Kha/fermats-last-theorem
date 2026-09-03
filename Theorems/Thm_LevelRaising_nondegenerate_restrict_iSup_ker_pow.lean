import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import P2M.Util
import P2M.Sol.S_LevelRaising_nondegenerate_restrict_iSup_ker_pow

set_option autoImplicit false
theorem LevelRaising.nondegenerate_restrict_iSup_ker_pow
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V)
    (hBl : ∀ x, (∀ y, B x y = 0) → x = 0) (hBr : ∀ y, (∀ x, B x y = 0) → y = 0)
    (g : Module.End F V) (hadj : ∀ x y, B (g x) y = B x (g y)) :
    (∀ x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n),
        (∀ y ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), B x y = 0) → x = 0) ∧
      (∀ y ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n),
        (∀ x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), B x y = 0) → y = 0) := by p2m_exact_reverting @_root_.P2MW.S_LevelRaising_nondegenerate_restrict_iSup_ker_pow.solution
