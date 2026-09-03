import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_antipode_comp_algEquiv_of_comul_compat

open scoped TensorProduct in
theorem HopfAlgebra.antipode_comp_algEquiv_of_comul_compat
    (K : Type*) [CommRing K]
    (H₁ : Type*) [CommRing H₁] [HopfAlgebra K H₁]
    (H₂ : Type*) [CommRing H₂] [HopfAlgebra K H₂]
    (φ : H₁ ≃ₐ[K] H₂)
    (hφcomul : ∀ x, Coalgebra.comul (R := K) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) :
    ∀ x, φ (HopfAlgebra.antipode K x) = HopfAlgebra.antipode K (φ x) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_antipode_comp_algEquiv_of_comul_compat.solution
