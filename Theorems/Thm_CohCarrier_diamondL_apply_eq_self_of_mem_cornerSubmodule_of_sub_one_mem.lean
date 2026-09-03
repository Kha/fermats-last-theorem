import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_CohCarrier_Inst
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.GroupTheory.Index
import P2M.Util
import P2M.Sol.S_CohCarrier_diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem

set_option autoImplicit false

p2m_open "CohCarrier IharaLemma~smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one IsLocalRing"

theorem CohCarrier.diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ)
    (hunit : IsUnit ((H.index : ℕ) : 𝒪))
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 L H 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 L H 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)), x • m = 0) → x = 0)
    (d : (ZMod L)ˣ) (t : 𝕋) (ht : ∀ v : H1 L H 𝒪, t • v = diamondL L H 𝒪 d v) (h1 : t - 1 ∈ Sp.𝔪 i)
    (v : H1 L H 𝒪) (hv : v ∈ cornerSubmodule (M := H1 L H 𝒪) (Sp.e i)) :
    diamondL L H 𝒪 d v = v := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem.solution
