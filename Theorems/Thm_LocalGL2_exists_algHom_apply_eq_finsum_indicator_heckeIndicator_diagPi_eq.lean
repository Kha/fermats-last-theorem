import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import P2M.Util
import P2M.Sol.S_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq

set_option autoImplicit false

open scoped Pointwise
open LocalGL2 HeckePair

theorem LocalGL2.exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ S : HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ),
      (∀ (f : HeckeAlgebra (integralSubgroup R K) R₀) (a b : ℤ),
        (S f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) K ⧸ integralSubgroup R K,
          Set.indicator
            {c : GL (Fin 2) K ⧸ integralSubgroup R K | ∃ g : GL (Fin 2) K, QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ b}
            (fun c => (f : GL (Fin 2) K → R₀) (Quotient.out c)) c) ∧
      S (heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) =
        AddMonoidAlgebra.single (1, 0) (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) +
          AddMonoidAlgebra.single (0, 1) 1 ∧
      S (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS) = AddMonoidAlgebra.single (1, 1) 1 := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq.solution
