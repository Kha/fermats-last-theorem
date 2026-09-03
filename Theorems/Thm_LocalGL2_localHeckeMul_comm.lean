import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_GelfandInvolution
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import P2M.Util
import P2M.Sol.S_LocalGL2_localHeckeMul_comm

open Matrix LocalGL2 HeckePair
theorem LocalGL2.localHeckeMul_comm
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {R₀ : Type*} [CommRing R₀]
    (f₁ f₂ : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) :
    f₁ * f₂ = f₂ * f₁ := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_localHeckeMul_comm.solution
