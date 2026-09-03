import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_heckeAlgebra_exists_ringHom_ker_residue_comp_eq_ker_of_one_le

set_option autoImplicit false
theorem CuspForm.heckeAlgebra.exists_ringHom_ker_residue_comp_eq_ker_of_one_le
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 1 ≤ k) (S : Set ℕ) (hint : CuspForm.HasIntegralStructure N k)
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (θ : CuspForm.heckeAlgebra N k S →+* F) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪'),
      (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪' ∧
      ∃ χ : CuspForm.heckeAlgebra N k S →+* 𝒪',
        RingHom.ker ((IsLocalRing.residue 𝒪').comp χ) = RingHom.ker θ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_ker_residue_comp_eq_ker_of_one_le.solution
