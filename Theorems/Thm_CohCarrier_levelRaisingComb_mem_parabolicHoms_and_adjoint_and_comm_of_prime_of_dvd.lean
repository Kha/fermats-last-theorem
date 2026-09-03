import Definitions.Def_CuspForm_CornerPairingFamily
import P2M.Util
import P2M.Sol.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd
attribute [-instance] ModularCurve.PDPairing.isFreeGroup_inf ModularCurve.PDPairing.instFintypeCusp ModularCurve.PDPairing.iotaDeg0_range_finiteIndex ModularCurve.PDPairing.CentralExt.instInv ModularCurve.PDPairing.CentralExt.instGroup ModularCurve.PDPairing.CentralExt.instMul ModularCurve.PDPairing.CentralExt.instOne ModularCurve.PDPairing.Gamma0Upper_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper CohCarrier.GammaHLower_finiteIndex
attribute [-simp] ModularCurve.PDPairing.CentralExt.lift_apply ModularCurve.PDPairing.mem_Gamma0Upper ModularCurve.PDPairing.CentralExt.snd_apply ModularCurve.PDPairing.pairZ_apply ModularCurve.PDPairing.conjUpperMat_apply_11 ModularCurve.PDPairing.sect_snd ModularCurve.PDPairing.conjUpperMat_apply_10 HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪))
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : q ∣ N)
    (h1 : CohCarrier.LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq' : CohCarrier.LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q))ˣ) q) :

    (∀ φ : CohCarrier.H1 N ⊤ 𝒪, φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 →
      ((CohCarrier.iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          - (q : 𝒪) • CohCarrier.iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1) φ ∈
        ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH (N * q) ⊤) 𝒪) ∧
    (∀ ψ : CohCarrier.H1 (N * q) ⊤ 𝒪,
      ψ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH (N * q) ⊤) 𝒪 →
      ((CohCarrier.heckeTL N ⊤ 𝒪 q).comp (CohCarrier.jDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1)
          - (q : 𝒪) • CohCarrier.jDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq') ψ ∈
        ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪) ∧

    (∀ (x jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪))
        (y wx : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH (N * q) ⊤) 𝒪)),
      (wx : CohCarrier.H1 (N * q) ⊤ 𝒪) =
        ((CohCarrier.iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          - (q : 𝒪) • CohCarrier.iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1) (x : CohCarrier.H1 N ⊤ 𝒪) →
      (jy : CohCarrier.H1 N ⊤ 𝒪) =
        ((CohCarrier.heckeTL N ⊤ 𝒪 q).comp (CohCarrier.jDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1)
          - (q : 𝒪) • CohCarrier.jDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq') (y : CohCarrier.H1 (N * q) ⊤ 𝒪) →
      CuspForm.Bfam₀ 𝒪 N jy x = CuspForm.Bfam₀ 𝒪 (N * q) y wx) ∧

    (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ≠ q → ∀ φ : CohCarrier.H1 N ⊤ 𝒪,
      ((CohCarrier.iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          - (q : 𝒪) • CohCarrier.iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1) (CohCarrier.heckeT N ⊤ ℓ 𝒪 φ) =
        CohCarrier.heckeT (N * q) ⊤ ℓ 𝒪
          (((CohCarrier.iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
            - (q : 𝒪) • CohCarrier.iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1) φ)) ∧

    (∀ (S : Set ℕ) (b : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)),
      b ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily N ⊤ S 𝒪)) →
      (∀ x : CohCarrier.H1 N ⊤ 𝒪, x ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 →
        b x ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪) ∧
      (∀ (x y bx by' : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪)),
        (bx : CohCarrier.H1 N ⊤ 𝒪) = b (x : CohCarrier.H1 N ⊤ 𝒪) →
        (by' : CohCarrier.H1 N ⊤ 𝒪) = b (y : CohCarrier.H1 N ⊤ 𝒪) →
        CuspForm.Bfam₀ 𝒪 N bx y = CuspForm.Bfam₀ 𝒪 N x by')) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.solution
