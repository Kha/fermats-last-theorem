import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero

open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_eq_coeff_zero
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ φ : ↥(chartAlgInf N ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(GaloisRep.ratLocalizedAt ℓ),
      ∀ x : ↥(chartAlgInf N ℓ),
        ((φ x : ↥(GaloisRep.ratLocalizedAt ℓ)) : ℚ) =
          ((x : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.solution
