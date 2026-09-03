import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le
attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

open scoped MatrixGroups TensorProduct

theorem CohCarrier.exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (κ : Type) [Field κ] [CharP κ p] :
    ∃ ι : κ ⊗[ℤ] ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) ℤ) →ₗ[κ]
        CohCarrier.H1 N ⊥ κ,
      (∀ (r : κ) (x : ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) ℤ))
          (γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))),
          ι (r ⊗ₜ[ℤ] x) (Additive.ofMul γ) =
            r * ((x : Additive ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) →+ ℤ) (Additive.ofMul γ) : κ)) ∧
      Function.Injective ι ∧
      LinearMap.range ι = ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) κ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le.solution
