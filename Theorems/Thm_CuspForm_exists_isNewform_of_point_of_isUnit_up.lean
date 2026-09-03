import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isNewform_of_point_of_isUnit_up
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply

theorem CuspForm.exists_isNewform_of_point_of_isUnit_up
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪']
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (hpN : p ∣ N) (up : 𝒪')
    (hup : ∃ χ' : CuspForm.heckeAlgebra N 2 ((↑S : Set ℕ) \ {p}) →+* 𝒪',
      (∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
        χ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono Set.diff_subset) t) = χ t) ∧
      χ' (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpN (by simp)) = up)
    (hunit : IsUnit up) :
    ∃ (Mg : ℕ) (_ : NeZero Mg) (hMgN : Mg ∣ N)
      (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (_ : g.IsNewform)
      (chig : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →+* ℂ)
      (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
        chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS) = ModularFormClass.qCoeff g ℓ)
      (iota : chig.range →+* 𝒪'),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
          (fun h => hℓN (h.trans hMgN)) (fun h => hℓS (Set.mem_of_mem_diff h)))) =
          χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
      ((∃ hpMg : ¬ p ∣ Mg,
          up * up - iota (chig.rangeRestrict
            (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpMg (by simp))) * up + (p : 𝒪') = 0) ∨
       (∃ hpMg : p ∣ Mg, ¬ p ^ 2 ∣ Mg ∧
          iota (chig.rangeRestrict
            (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpMg (by simp))) = up)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isNewform_of_point_of_isUnit_up.solution
