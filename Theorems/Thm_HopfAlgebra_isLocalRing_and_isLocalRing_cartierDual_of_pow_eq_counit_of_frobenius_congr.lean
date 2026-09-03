import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr

theorem HopfAlgebra.isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr
    {R : Type*} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (H : Type*) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    [Coalgebra.IsCocomm R H]
    (t : H →ₐc[R] H)
    (ht : ∃ m : ℕ, ∀ a : H, (t ^ m) a = algebraMap R H (Coalgebra.counit a))
    (hF : ∀ a : H, (p : H) ∣ t a ^ p - a ^ (p ^ 2))
    (hV : ∀ φ : H →ₗ[R] R, (p : WithConv (H →ₗ[R] R)) ∣
        WithConv.toConv (φ ∘ₗ (t : H →ₗ[R] H)) ^ p - WithConv.toConv φ ^ (p ^ 2)) :
    IsLocalRing H ∧ IsLocalRing (CartierDual R H) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr.solution
