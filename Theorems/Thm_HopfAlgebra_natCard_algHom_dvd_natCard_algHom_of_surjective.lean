import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_natCard_algHom_dvd_natCard_algHom_of_surjective

set_option autoImplicit false

theorem HopfAlgebra.natCard_algHom_dvd_natCard_algHom_of_surjective
    (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K]
    (H : Type) [CommRing H] [HopfAlgebra R H]
    (H₀ : Type) [CommRing H₀] [HopfAlgebra R H₀]
    (π : H →ₐc[R] H₀) (hπ : Function.Surjective π) [Finite (H →ₐ[R] K)] :
    Nat.card (H₀ →ₐ[R] K) ∣ Nat.card (H →ₐ[R] K) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_natCard_algHom_dvd_natCard_algHom_of_surjective.solution
