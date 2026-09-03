import Definitions.Def_CuspForm_CornerPairingFamily
import P2M.Util
import P2M.Sol.S_CuspForm_Bfam_degeneracyBlock
attribute [-instance] ModularCurve.PDPairing.isFreeGroup_inf ModularCurve.PDPairing.instFintypeCusp ModularCurve.PDPairing.iotaDeg0_range_finiteIndex ModularCurve.PDPairing.CentralExt.instInv ModularCurve.PDPairing.CentralExt.instGroup ModularCurve.PDPairing.CentralExt.instMul ModularCurve.PDPairing.CentralExt.instOne ModularCurve.PDPairing.Gamma0Upper_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] ModularCurve.PDPairing.CentralExt.lift_apply ModularCurve.PDPairing.mem_Gamma0Upper ModularCurve.PDPairing.CentralExt.snd_apply ModularCurve.PDPairing.pairZ_apply ModularCurve.PDPairing.conjUpperMat_apply_11 ModularCurve.PDPairing.sect_snd ModularCurve.PDPairing.conjUpperMat_apply_10 HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

open CohCarrier

theorem CuspForm.Bfam.degeneracyBlock
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    ∀ (M M' : ℕ) [NeZero M] [NeZero M'] (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ)
        (h₁ : LevelLE M M ⊤ H 1) (h₁' : LevelLE M' M' ⊤ H' 1)
        (d d' : ℕ) [NeZero d] [NeZero d'] (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
        (hdd' : d * d' = M' / M)
        (hH' : ∀ u : (ZMod M')ˣ, u ∈ H' ↔ ZMod.unitsMap h.dvd u ∈ H),
        IsUnit ((H.index : ℕ) : 𝒪) → IsUnit ((H'.index : ℕ) : 𝒪) →
        ∀ (x : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)))
          (y : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' ⊤) 𝒪).map (iDegL M' M' ⊤ H' 1 𝒪 𝒪 h₁')))
          (ix : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' ⊤) 𝒪).map (iDegL M' M' ⊤ H' 1 𝒪 𝒪 h₁')))
          (jy : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
        (ix : H1 M' H' 𝒪) = iDegL M M' H H' d 𝒪 𝒪 h x →
        (jy : H1 M H 𝒪) = jDegL M M' H H' d' 𝒪 𝒪 h' y →
        CuspForm.Bfam 𝒪 M H h₁ jy x = CuspForm.Bfam 𝒪 M' H' h₁' y ix := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_Bfam_degeneracyBlock.solution
