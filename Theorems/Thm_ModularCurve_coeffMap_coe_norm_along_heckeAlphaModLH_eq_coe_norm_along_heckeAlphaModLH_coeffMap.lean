import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap

set_option autoImplicit false

open ModularCurve AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap
    (k K : Type*) [Field k] [Field K] (j : k →+* K)
    (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (hfink : FiniteAlong k (heckeAlphaModLH k N H ℓ)) (hfinK : FiniteAlong K (heckeAlphaModLH K N H ℓ))
    (hdeg : finrankAlong k (heckeAlphaModLH k N H ℓ) = finrankAlong K (heckeAlphaModLH K N H ℓ))
    (x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) :
    coeffMap j (((letI := algebraAlong (heckeAlphaModLH k N H ℓ)
        Algebra.norm ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)) x) : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H))) : LaurentSeries k) =
      (((letI := algebraAlong (heckeAlphaModLH K N H ℓ)
        Algebra.norm ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H))
          (⟨coeffMap j (x : LaurentSeries k),
            coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) x.2⟩ :
            ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))))) :
          ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H))) : LaurentSeries K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap.solution
