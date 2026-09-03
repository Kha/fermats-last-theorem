import Definitions.Def_ModularCurve_HeckeNamedInputs
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one

set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.heckeBetaRoof_adjoin_range_union_eq_top
    (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ)
    [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (hM : M = N * ℓ * ℓ')
    (hgenQ : FunctionFieldGeneration M) (data : ModularPolynomialData ℓ) (data' : ModularPolynomialData ℓ') :
    Algebra.adjoin L
      (Set.range (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2)
        ∪ Set.range (towerSubstBar L (N * ℓ) ℓ' (dvd_of_eq_roof_beta N ℓ ℓ' M hM).1)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top.solution
