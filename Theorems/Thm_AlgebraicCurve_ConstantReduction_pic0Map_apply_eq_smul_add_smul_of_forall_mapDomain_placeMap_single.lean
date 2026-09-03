import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (𝓡 : ConstantReduction A F Fbar)
    (T : Divisor L F →+ Divisor L F)
    (hT0 : ∀ D : Divisor L F, D ∈ Divisor.degZero (K := L) (F := F) → T D ∈ Divisor.degZero (K := L) (F := F))
    (TJ : Pic0 L F → Pic0 L F)
    (hTJ : ∀ D : Divisor.degZero (K := L) (F := F), TJ (Pic0.mk D) = Pic0.mk ⟨T (D : Divisor L F), hT0 D D.2⟩)
    (g : SemilinearAut (IsLocalRing.ResidueField ↥A) Fbar) (ℓ : ℕ)
    (hplace : ∀ P : Place L F, Finsupp.mapDomain 𝓡.placeMap (T (Finsupp.single P 1)) =
      Finsupp.single (g • 𝓡.placeMap P) 1 + ℓ • Finsupp.single (g⁻¹ • 𝓡.placeMap P) 1) :
    ∀ c : Pic0 L F, 𝓡.pic0Map (TJ c) = g • 𝓡.pic0Map c + ℓ • (g⁻¹ • 𝓡.pic0Map c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single.solution
