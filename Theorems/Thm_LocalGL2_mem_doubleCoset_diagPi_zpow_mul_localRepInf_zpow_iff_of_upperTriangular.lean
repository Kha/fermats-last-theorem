import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import P2M.Util
import P2M.Sol.S_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular

set_option autoImplicit false

open Matrix LocalGL2 HeckePair

theorem LocalGL2.mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (hϖ0 : algebraMap R K ϖ ≠ 0)
    (g : GL (Fin 2) K) (u₁ u₂ : Rˣ) (a b : ℤ)
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K u₁ * algebraMap R K ϖ ^ a)
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K u₂ * algebraMap R K ϖ ^ b)
    {m n : ℤ} (hmn : m ≤ n) :
    g ∈ doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n) ↔
      m + n = a + b ∧ m ≤ min a b ∧
        (∃ r : R, (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K ϖ ^ m * algebraMap R K r) ∧
        (m < min a b →
          ¬ ∃ r : R, (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K ϖ ^ (m + 1) * algebraMap R K r) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular.solution
