import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_LocalGL2_iwasawa_decomposition

theorem LocalGL2.iwasawa_decomposition (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (g : GL (Fin 2) K) :
    ∃ b k : GL (Fin 2) K, k ∈ LocalGL2.integralSubgroup R K ∧
      (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ g = b * k := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_iwasawa_decomposition.solution
