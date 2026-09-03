import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_counit_comp_algEquiv_of_comul_compat

open scoped TensorProduct in
theorem Bialgebra.counit_comp_algEquiv_of_comul_compat
    (K : Type*) [CommRing K]
    (B₁ : Type*) [CommRing B₁] [Bialgebra K B₁]
    (B₂ : Type*) [CommRing B₂] [Bialgebra K B₂]
    (φ : B₁ ≃ₐ[K] B₂)
    (hφcomul : ∀ x, Coalgebra.comul (R := K) (φ x) =
        (_root_.TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) :
    ∀ x, Coalgebra.counit (R := K) (φ x) = Coalgebra.counit (R := K) x := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_counit_comp_algEquiv_of_comul_compat.solution
