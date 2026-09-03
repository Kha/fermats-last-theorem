import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iotaInf_comap

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IntermediateField IsDedekindDomain AlgebraicCurve AlgebraicCurve.CurveModel
theorem AlgebraicCurve.CurveModel.placeOfPoint_ofGenerator_iotaInf_comap
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀⁻¹} : Set L₀) →+* chartRing K ({t⁻¹} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀⁻¹} : Set L₀), φ (a : L₀) = (ψ a : L))
    (x : closedPoints (CurveModel.ofGenerator K t ht).C) (hx : x.1 ∉ Set.range (ι₀ K t).base)
    (xb : XInf K t) (hxb : (ιInf K t).base xb = x.1)
    (y : closedPoints (CurveModel.ofGenerator K₀ t₀ ht₀).C) (hy : y.1 ∉ Set.range (ι₀ K₀ t₀).base)
    (yb : XInf K₀ t₀) (hyb : (ιInf K₀ t₀).base yb = y.1)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    ((CurveModel.ofGenerator K t ht).placeOfPoint x).toValuationSubring.toSubring.comap φ =
      ((CurveModel.ofGenerator K₀ t₀ ht₀).placeOfPoint y).toValuationSubring.toSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iotaInf_comap.solution
