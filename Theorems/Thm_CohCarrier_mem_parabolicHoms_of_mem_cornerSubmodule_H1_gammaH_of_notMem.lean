import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false
open scoped IsMulCommutative in

theorem CohCarrier.mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N H S 𝒪 g * CohCarrier.opFamily N H S 𝒪 h =
        CohCarrier.opFamily N H S 𝒪 h * CohCarrier.opFamily N H S 𝒪 g)
    (θbar : CohCarrier.Gen N S → k)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N H S 𝒪 k hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N) (hℓ1 : ℓ ≡ 1 [MOD N])
    (hnot : (⟨(CohCarrier.hdata N H S 𝒪 k hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ -
            ((ℓ : ↥(CohCarrier.hdata N H S 𝒪 k hcomm θbar).opSubalgebra) + 1)) ∉ Sp.𝔪 i₀)
    (hstab : ∀ (g : CohCarrier.Gen N S) (ψ : CohCarrier.H1 N H 𝒪),
      ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪 →
        CohCarrier.opFamily N H S 𝒪 g ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪)
    (φ : CohCarrier.H1 N H 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N H 𝒪) (Sp.e i₀)) :
    φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N H) 𝒪 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_gammaH_of_notMem.solution
