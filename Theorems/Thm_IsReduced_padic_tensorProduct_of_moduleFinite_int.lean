import Mathlib
import P2M.Util
import P2M.Sol.S_IsReduced_padic_tensorProduct_of_moduleFinite_int
set_option autoImplicit false

theorem IsReduced.padic_tensorProduct_of_moduleFinite_int
    (S : Type*) [CommRing S] [Module.Finite ℤ S] [Module.Free ℤ S] [IsReduced S] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsReduced (TensorProduct ℤ ℚ_[ℓ] S) := by p2m_exact_reverting @_root_.P2MW.S_IsReduced_padic_tensorProduct_of_moduleFinite_int.solution
