import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_LocalGL2_finite_image_integralSubgroup_mul_singleton

open scoped Pointwise
open LocalGL2
theorem LocalGL2.finite_image_integralSubgroup_mul_singleton
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (g : GL (Fin 2) K) :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_finite_image_integralSubgroup_mul_singleton.solution
