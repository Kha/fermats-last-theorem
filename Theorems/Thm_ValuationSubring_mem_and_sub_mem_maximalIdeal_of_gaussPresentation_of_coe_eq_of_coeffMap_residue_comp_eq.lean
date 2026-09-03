import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq

set_option autoImplicit false

open ModularCurve IsLocalRing

theorem ValuationSubring.mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq
    {L : Type} [Field L] (A : ValuationSubring L)
    (F : IntermediateField L (LaurentSeries L))
    (O : ValuationSubring F)
    (hO : ∀ f : F, f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x)
    (Φ : LaurentSeries L →+* LaurentSeries L) (Ψ : LaurentSeries A →+* LaurentSeries A)
    (hΦΨ : ∀ y : LaurentSeries A, Φ (coeffMap A.subtype y) = coeffMap A.subtype (Ψ y))
    (hΨ : ∀ y : LaurentSeries A, coeffMap (IsLocalRing.residue A) (Ψ y) = coeffMap (IsLocalRing.residue A) y)
    (T : F →+* F) (hT : ∀ f : F, ((T f : F) : LaurentSeries L) = Φ (f : LaurentSeries L))
    (f : F) (hf : f ∈ O) :
    ∃ hTf : T f ∈ O, (⟨T f, hTf⟩ : O) - ⟨f, hf⟩ ∈ IsLocalRing.maximalIdeal O := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq.solution
