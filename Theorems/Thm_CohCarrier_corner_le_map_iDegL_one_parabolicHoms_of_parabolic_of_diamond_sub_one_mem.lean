import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_corner_le_map_iDegL_one_parabolicHoms_of_parabolic_of_diamond_sub_one_mem

set_option autoImplicit false

open CohCarrier hiding mem_map_iDegL_one_parabolicHoms_iff open IharaLemma

theorem CohCarrier.corner_le_map_iDegL_one_parabolicHoms_of_parabolic_of_diamond_sub_one_mem
    {𝒪 : Type} [CommRing 𝒪] (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ Hs 1)
    (hunit : IsUnit ((Hs.index : ℕ) : 𝒪))
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M Hs 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M Hs 𝒪)]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    (hpar : ∀ v : H1 M Hs 𝒪, v ∈ cornerSubmodule (M := H1 M Hs 𝒪) (Sp.e i) →
      v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪)
    (hneb : ∀ d : (ZMod M)ˣ, ∃ g : 𝕋, (∀ v : H1 M Hs 𝒪, g • v = diamondL M Hs 𝒪 d v) ∧ g - 1 ∈ Sp.𝔪 i) :
    ∀ v : H1 M Hs 𝒪, v ∈ cornerSubmodule (M := H1 M Hs 𝒪) (Sp.e i) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ Hs 1 𝒪 𝒪 h₁) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_corner_le_map_iDegL_one_parabolicHoms_of_parabolic_of_diamond_sub_one_mem.solution
