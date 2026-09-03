import Definitions.Def_ModularCurve_PDPairing
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_PDPairing_heckeT0_apply_eq_heckeT_top_apply
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero
set_option autoImplicit false
open scoped MatrixGroups in

theorem ModularCurve.PDPairing.heckeT0_apply_eq_heckeT_top_apply (N ℓ : ℕ) [NeZero ℓ]
    (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N ⊤ A) (ψ : Additive ↥(CongruenceSubgroup.Gamma0 N) →+ A)
    (hφψ : ∀ γ : ↥(CohCarrier.GammaH N ⊤),
      φ (Additive.ofMul γ) =
        ψ (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩))
    (γ : ↥(CohCarrier.GammaH N ⊤)) :
    ModularCurve.PDPairing.heckeT0 N ℓ A ψ
        (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) =
      CohCarrier.heckeT N ⊤ ℓ A φ (Additive.ofMul γ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PDPairing_heckeT0_apply_eq_heckeT_top_apply.solution
