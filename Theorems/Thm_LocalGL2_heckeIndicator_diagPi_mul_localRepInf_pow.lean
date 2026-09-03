import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import P2M.Util
import P2M.Sol.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow

open scoped Pointwise
open LocalGL2 HeckePair
theorem LocalGL2.heckeIndicator_diagPi_mul_localRepInf_pow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀] (k : ℕ)
    (hk2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 2)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hk3 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 3)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hSk : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)}) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 2)) hk2
      = (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 3)) hk3 : HeckeAlgebra (integralSubgroup R K) R₀)
        + (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀)
          • heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) hSk := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.solution
