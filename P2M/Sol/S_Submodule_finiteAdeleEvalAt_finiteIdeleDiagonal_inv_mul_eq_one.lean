import Definitions.Def_Submodule_LocalBox
import P2M.Util
namespace P2MW.S_Submodule_finiteAdeleEvalAt_finiteIdeleDiagonal_inv_mul_eq_one

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D] (w : HeightOneSpectrum (𝓞 ℚ)) (γ : Dˣ)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (γ : D) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) :
    Submodule.finiteAdeleEvalAt D w
      (((Submodule.finiteIdeleDiagonal D γ)⁻¹ * g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
  rw [Units.val_mul, map_mul, hg, ← map_inv, Submodule.val_finiteIdeleDiagonal_apply, Submodule.finiteAdeleEvalAt_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, Algebra.TensorProduct.one_def]
  congr 1
  exact one_mul _
