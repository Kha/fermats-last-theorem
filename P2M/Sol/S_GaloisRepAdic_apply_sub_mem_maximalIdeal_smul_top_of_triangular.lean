import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
namespace P2MW.S_GaloisRepAdic_apply_sub_mem_maximalIdeal_smul_top_of_triangular

set_option autoImplicit false

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] (ρ : GaloisRepAdic B)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Module.Basis (Fin 2) B ρ.V) (x y z : B)
    (h0 : ρ.ρ σ (b 0) = x • b 0) (h1 : ρ.ρ σ (b 1) = y • b 0 + z • b 1)
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal B) (hy : y ∈ IsLocalRing.maximalIdeal B)
    (hz : z - 1 ∈ IsLocalRing.maximalIdeal B) (v : ρ.V) :
    ρ.ρ σ v - v ∈ (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B ρ.V) := by

  have hv : v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two]
  have key : ρ.ρ σ v - v =
      (b.repr v 0 * (x - 1) + b.repr v 1 * y) • b 0 + (b.repr v 1 * (z - 1)) • b 1 := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, h0, h1]
    module
  rw [key]
  exact Submodule.add_mem _
    (Submodule.smul_mem_smul
      ((IsLocalRing.maximalIdeal B).add_mem ((IsLocalRing.maximalIdeal B).mul_mem_left _ hx)
        ((IsLocalRing.maximalIdeal B).mul_mem_left _ hy))
      Submodule.mem_top)
    (Submodule.smul_mem_smul ((IsLocalRing.maximalIdeal B).mul_mem_left _ hz) Submodule.mem_top)
