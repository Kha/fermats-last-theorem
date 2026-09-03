import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type w} [Fintype ι] (σ : ι → (Spec (CommRingCat.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart) (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ [AlgebraicCurve.IsCurveOver k X.functionField]
      [∀ v : AlgebraicCurve.Place k X.functionField, v.DCoordGenerates]
      [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := X.functionField)]
      (hRT : AlgebraicCurve.ResidueTheorem k X.functionField),
    ∃ (_ : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens))
      (hW : AlgebraicCurve.placesOf c 𝒱.U1 ∪ AlgebraicCurve.placesOf c 𝒱.U0 = Set.univ)
      (hgerm : ∀ s : (𝒱.cover c).A01, (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c 𝒱.U1 ∩ AlgebraicCurve.placesOf c 𝒱.U0)
          (0 : AlgebraicCurve.Divisor k X.functionField))
      (e1 : (𝒱.structureSheafSections c).H1 →ₗ[k]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf c 𝒱.U1) (AlgebraicCurve.placesOf c 𝒱.U0)
          (0 : AlgebraicCurve.Divisor k X.functionField))
      (_ : ∀ s : (𝒱.cover c).A01, e1 (Submodule.Quotient.mk s) =
        Submodule.Quotient.mk ⟨(X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom s, hgerm s⟩)
      (eΩ : (𝒱.kaehlerSections c).H0 →ₗ[k] ↥(AlgebraicCurve.regularDifferentials k X.functionField))
      (_ : Nonempty (𝒱.U0 : X.Opens))
      (_ : ∀ ω : (𝒱.kaehlerSections c).H0,
        ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k X.functionField)) : Ω[X.functionField⁄k]) =
          AlgebraicCurve.kaehlerToFunctionField c 𝒱.U0 ω.val.1),
      ∀ (ω : (𝒱.kaehlerSections c).H0) (x : (𝒱.structureSheafSections c).H1),
        (𝒱.cover c).serrePairingInt Λ hv ω x = AlgebraicCurve.serrePairing hRT hW (eΩ ω) (e1 x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong.solution

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
