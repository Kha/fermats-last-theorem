import Definitions.Def_AlgebraicGeometry_KwPthPowerKerDExpansionEngine
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_KwPke_kw_pke_hsep_of_isSeparable_adjoin

theorem AlgebraicCurve.KwPke.kw_pke_hsep_of_isSeparable_adjoin
    {K F : Type*} [Field K] [Field F] [Algebra K F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ]
    [PerfectField K] (t : F)
    (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F) :
    ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_KwPke_kw_pke_hsep_of_isSeparable_adjoin.solution
