import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PDPairing
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CongruenceSubgroup ModularCurve.Period

theorem CohCarrier.exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
    (N : ℕ) [NeZero N] (𝒪 : Type) [CommRing 𝒪] [IsAddTorsionFree 𝒪] :
    ∃ ι : 𝒪 ⊗[ℤ] ↥(parabolicHoms ℤ (Gamma0 N) ℤ) →ₗ[𝒪] CohCarrier.H1 N ⊤ 𝒪,
      (∀ (r : 𝒪) (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) (γ : ↥(CohCarrier.GammaH N ⊤)),
          ι (r ⊗ₜ[ℤ] x) (Additive.ofMul γ) =
            r * ((x : Additive ↥(Gamma0 N) →+ ℤ)
              (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) : 𝒪)) ∧
      Function.Injective ι ∧
      LinearMap.range ι = parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (r : 𝒪) (x y : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)),
        (y : Additive ↥(Gamma0 N) →+ ℤ) =
            ModularCurve.PDPairing.heckeT0 N ℓ ℤ (x : Additive ↥(Gamma0 N) →+ ℤ) →
          ι (r ⊗ₜ[ℤ] y) = CohCarrier.heckeT N ⊤ ℓ 𝒪 (ι (r ⊗ₜ[ℤ] x)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top.solution
