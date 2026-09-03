import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong
attribute [-simp] AlgebraicCurve.serrePairing_apply_mk AlgebraicCurve.residueSumOffChartLinear_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve hiding sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong open ModularCurve KaehlerDifferential

theorem ModularCurve.sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    [HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)] [HasCanonicalLocalResidueKStar K ↥(charLDegeneracyRoof K N ℓ)] [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    [∀ v : Place K ↥(modularFunctionFieldC K N), v.DCoordGenerates] [∀ w : Place K ↥(charLDegeneracyRoof K N ℓ), w.DCoordGenerates]
    [Nontrivial Ω[↥(modularFunctionFieldC K N)⁄K]] [Nontrivial Ω[↥(charLDegeneracyRoof K N ℓ)⁄K]]
    (hαI : HeckeAlphaCIntegral K N ℓ) (hβI : HeckeBetaCIntegral K N ℓ)
    (hFα : FibreResidueIdentityAlong (heckeAlphaC K N ℓ) hαI) (hFβ : FibreResidueIdentityAlong (heckeBetaC K N ℓ) hβI)
    (hsep : SeparableAlong K (heckeBetaC K N ℓ))
    (hΩ : ∀ η : Ω[↥(charLDegeneracyRoof K N ℓ)⁄K], ∃ (ω₁ : Ω[↥(modularFunctionFieldC K N)⁄K]) (c : ↥(charLDegeneracyRoof K N ℓ)), η = c • Differential.pullbackAlong (heckeBetaC K N ℓ) ω₁)
    (SS : Finset (Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K)
    (hstab : ∀ w : Place K ↥(charLDegeneracyRoof K N ℓ),
      Place.restrictAlong (heckeAlphaC K N ℓ) hαI w ∈ SS ↔ Place.restrictAlong (heckeBetaC K N ℓ) hβI w ∈ SS)
    (m : ℕ) (hm : 1 ≤ m) (u : ↥(charLDegeneracyRoof K N ℓ)) (gv f₁ : ↥(modularFunctionFieldC K N)) (ω : Ω[↥(modularFunctionFieldC K N)⁄K])
    (hSP : ∀ x : SSIndex p N K hp5 (2 * (m : ℤ)),
      f₁ - traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u) = 0 ∨
        -(ModularCurve.weightDivisor K N m x.1) + 1 ≤ x.1.ord (f₁ - traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u)))
    (hLT : ∀ x ∈ SS, ¬ ((placeWidth N x : ℤ) ∣ (m : ℤ)) →
      f₁ - traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u) = 0 ∨
        -(ModularCurve.weightDivisor K N m x) ≤ x.ord (f₁ - traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u)))
    (hωi : ∀ x : SSIndex p N K hp5 (2 * (m : ℤ)), ModularCurve.weightDivisor K N m x.1 - 1 ≤ x.1.ordDifferential ω)
    (hωn : ∀ x ∈ SS, ¬ ((placeWidth N x : ℤ) ∣ (m : ℤ)) → ModularCurve.weightDivisor K N m x ≤ x.ordDifferential ω) :
    ∑ x ∈ SS, kaehlerResidueTerm ω (diagonalHom K ↥(modularFunctionFieldC K N) f₁) x
      = ∑ z ∈ SS, kaehlerResidueTerm
          (Differential.traceAlong (heckeBetaC K N ℓ) (u • Differential.pullbackAlong (heckeAlphaC K N ℓ) ω))
          (diagonalHom K ↥(modularFunctionFieldC K N) gv) z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong.solution
