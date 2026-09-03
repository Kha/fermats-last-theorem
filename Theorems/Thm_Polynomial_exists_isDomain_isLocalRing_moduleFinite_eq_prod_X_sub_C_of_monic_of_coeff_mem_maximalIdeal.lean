import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_Polynomial_exists_isDomain_isLocalRing_moduleFinite_eq_prod_X_sub_C_of_monic_of_coeff_mem_maximalIdeal

set_option autoImplicit false

p2m_open "FormalGroup IsLocalRing~of_isDomain_of_moduleFinite_of_isAdicComplete"

theorem Polynomial.exists_isDomain_isLocalRing_moduleFinite_eq_prod_X_sub_C_of_monic_of_coeff_mem_maximalIdeal
    {S : Type} [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    (P : Polynomial S) (hP : P.Monic) (hdeg : 0 < P.natDegree)
    (hP𝔪 : ∀ i : ℕ, i < P.natDegree → P.coeff i ∈ maximalIdeal S) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : Algebra S V) (_ : Module.Finite S V)
      (_ : IsAdicComplete (maximalIdeal V) V),
      Function.Injective (algebraMap S V) ∧ (maximalIdeal S).map (algebraMap S V) ≤ maximalIdeal V ∧
      ∃ r : Fin P.natDegree → V, (∀ i, r i ∈ maximalIdeal V) ∧
        P.map (algebraMap S V) = ∏ i, (Polynomial.X - Polynomial.C (r i)) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_isDomain_isLocalRing_moduleFinite_eq_prod_X_sub_C_of_monic_of_coeff_mem_maximalIdeal.solution
