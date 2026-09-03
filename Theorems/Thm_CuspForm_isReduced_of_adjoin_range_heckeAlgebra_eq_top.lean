import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_isReduced_of_adjoin_range_heckeAlgebra_eq_top
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

theorem CuspForm.isReduced_of_adjoin_range_heckeAlgebra_eq_top
    {N : ℕ} [NeZero N] {S : Set ℕ} (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (π : CuspForm.heckeAlgebra N 2 S →+* T) (hadj : Algebra.adjoin 𝒪 (Set.range π) = ⊤) :
    IsReduced T := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_isReduced_of_adjoin_range_heckeAlgebra_eq_top.solution
