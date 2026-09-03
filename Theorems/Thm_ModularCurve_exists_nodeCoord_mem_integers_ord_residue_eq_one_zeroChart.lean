import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart
    (p : ℕ) [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField ↥A) p]
    {Fbar : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (C : ComponentChart A ↥(modularFunctionFieldBar p) Fbar)
    (X : Fbar) (xpl : IsLocalRing.ResidueField ↥A → Place (IsLocalRing.ResidueField ↥A) Fbar)
    (hord_poly : ∀ (c : IsLocalRing.ResidueField ↥A) (P : Polynomial (IsLocalRing.ResidueField ↥A)),
      (xpl c).ord (Polynomial.aeval X P) = (P.rootMultiplicity c : ℤ))
    (hjF : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ∈ C.integers)
    (hjpF : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : modularFunctionFieldBar p) ∈ C.integers)
    (hres_jp : C.residue ⟨_, hjpF⟩ = X) (hres_j : C.residue ⟨_, hjF⟩ = X ^ p)
    (a : IsLocalRing.ResidueField ↥A) (ha2 : a ^ (p ^ 2) = a) :
    ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full p (dvd_refl p))⟩ : modularFunctionFieldBar p)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ^ p
        ∈ C.integers,
      (xpl (a ^ p)).ord (C.residue ⟨_, h⟩) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart.solution
