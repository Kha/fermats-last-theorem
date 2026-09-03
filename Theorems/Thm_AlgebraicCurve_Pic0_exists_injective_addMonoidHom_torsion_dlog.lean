import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_dlog
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

theorem AlgebraicCurve.Pic0.exists_injective_addMonoidHom_torsion_dlog
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : F) (ht : Transcendental K t) [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (hdt : KaehlerDifferential.D K F t ≠ 0) :
    ∃ φ : AlgebraicCurve.Pic0.torsion K F p →+ Ω[F⁄K], Function.Injective φ ∧
      ∀ c, ∃ f : F, f ≠ 0 ∧ (∀ v : AlgebraicCurve.Place K F, (p : ℤ) ∣ v.ord f) ∧
        φ c = f⁻¹ • KaehlerDifferential.D K F f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_dlog.solution
