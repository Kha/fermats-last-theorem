import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi

set_option autoImplicit false

open scoped Pointwise
open LocalGL2

theorem HeckeIntegralSeam.exists_isHeckeCosetSystem_integralSubgroup_diagPi
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (hϖ0 : algebraMap R K ϖ ≠ 0) :
    ∃ (n : ℕ) (rT : Fin n → GL (Fin 2) K),
      HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup R K) (LocalGL2.diagPi ϖ hϖ0) rT := by p2m_exact_reverting @_root_.P2MW.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi.solution
