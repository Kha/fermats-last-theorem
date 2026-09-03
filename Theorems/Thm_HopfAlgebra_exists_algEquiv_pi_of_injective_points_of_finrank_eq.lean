import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_algEquiv_pi_of_injective_points_of_finrank_eq

theorem HopfAlgebra.exists_algEquiv_pi_of_injective_points_of_finrank_eq
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H] [Coalgebra.IsCocomm O H]
    (k : ℕ) (htors : ∀ x : WithConv (H →ₐ[O] O), x ^ ℓ ^ k = 1)
    (hinv : ∀ x : WithConv (H →ₐ[O] O), ∃ z : WithConv (H →ₐ[O] O), x * z = 1 ∧ z * x = 1)
    {ι : Type*} [Fintype ι] (y : ι → WithConv (H →ₐ[O] O)) (hy : Function.Injective y)
    (hrank : Module.finrank O H = Fintype.card ι) :
    ∃ φ : H ≃ₐ[O] (ι → O), ∀ (a : H) (i : ι), φ a i = y i a := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_algEquiv_pi_of_injective_points_of_finrank_eq.solution
