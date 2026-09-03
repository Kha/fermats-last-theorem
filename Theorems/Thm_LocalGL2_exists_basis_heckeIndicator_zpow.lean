import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import P2M.Util
import P2M.Sol.S_LocalGL2_exists_basis_heckeIndicator_zpow

open scoped Pointwise
open LocalGL2 HeckePair
theorem LocalGL2.exists_basis_heckeIndicator_zpow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ)
    {R₀ : Type*} [CommRing R₀]
    (hfin : ∀ g : GL (Fin 2) K,
      (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
        Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ b : Module.Basis {p : ℤ × ℤ // p.1 ≤ p.2} R₀ (HeckeAlgebra (integralSubgroup R K) R₀),
      ∀ p, b p = heckeIndicator R₀ (diagPi ϖ hϖ0 ^ p.1.1 * localRepInf ϖ hϖ0 ^ p.1.2) (hfin _) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_exists_basis_heckeIndicator_zpow.solution
