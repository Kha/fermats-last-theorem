import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import P2M.Util
import P2M.Sol.S_LocalGL2_heckeIndicator_diagPi_mul_self

open scoped Pointwise
open LocalGL2 HeckePair
theorem LocalGL2.heckeIndicator_diagPi_mul_self
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (h2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ 2}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
      = (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ 2) h2 : HeckeAlgebra (integralSubgroup R K) R₀)
        + ((Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) + 1)
          • heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_self.solution
