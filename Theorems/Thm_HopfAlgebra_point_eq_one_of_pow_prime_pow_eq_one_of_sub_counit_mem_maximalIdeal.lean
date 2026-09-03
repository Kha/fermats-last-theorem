import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal

theorem HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H] [Coalgebra.IsCocomm O H]
    (x : WithConv (H →ₐ[O] O))
    (hx1 : ∀ h : H, x h - algebraMap O O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O)
    (k : ℕ) (hxk : x ^ ℓ ^ k = 1) :
    x = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal.solution
