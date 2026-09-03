import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient

set_option autoImplicit false
theorem KummerTheory.natCard_algEquiv_eq_natCard_powerSubgroup_quotient (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {n : ℕ} (hμ : (primitiveRoots n K).Nonempty)
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Nat.card (L ≃ₐ[K] L)
      = Nat.card (groupCohomology.Kummer.powerSubgroup K L n ⧸
          ((powMonoidHom n : Kˣ →* Kˣ).range).subgroupOf (groupCohomology.Kummer.powerSubgroup K L n)) := by p2m_exact_reverting @_root_.P2MW.S_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient.solution
