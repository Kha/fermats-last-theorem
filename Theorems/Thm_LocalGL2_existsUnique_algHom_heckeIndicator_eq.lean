import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import P2M.Util
import P2M.Sol.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq

open scoped Pointwise
open LocalGL2 HeckePair
theorem LocalGL2.existsUnique_algHom_heckeIndicator_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    {A : Type*} [CommRing A] [Algebra R₀ A] (a : A) (b : Aˣ) :
    ∃! χ : HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] A,
      χ (heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) = a ∧
      χ (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS) = (b : A) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_existsUnique_algHom_heckeIndicator_eq.solution
