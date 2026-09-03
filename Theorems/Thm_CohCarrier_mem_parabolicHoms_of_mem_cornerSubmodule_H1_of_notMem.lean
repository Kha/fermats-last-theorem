import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_of_notMem
attribute [-instance] ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

set_option autoImplicit false

open scoped IsMulCommutative in

theorem CohCarrier.mem_parabolicHoms_of_mem_cornerSubmodule_H1_of_notMem
    (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 h =
        CohCarrier.opFamily N ⊤ S 𝒪 h * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → k)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N)
    (hℓ1 : ∀ t : ℕ, t * t ∣ N → ℓ ≡ 1 [MOD t])
    (hnot : (⟨(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓN),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ -
            ((ℓ : ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra) + 1)) ∉ Sp.𝔪 i₀)
    (φ : CohCarrier.H1 N ⊤ 𝒪)
    (hφ : φ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) :
    φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_mem_parabolicHoms_of_mem_cornerSubmodule_H1_of_notMem.solution
