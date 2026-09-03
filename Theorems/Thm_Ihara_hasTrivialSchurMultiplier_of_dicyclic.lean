import Mathlib.GroupTheory.OrderOfElement
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_hasTrivialSchurMultiplier_of_dicyclic

theorem Ihara.hasTrivialSchurMultiplier_of_dicyclic
    {G : Type*} [Group G] (x y : G) (m : ℕ)
    (hx : orderOf x = 2 * m) (hy : y ^ 2 = x ^ m) (hconj : y * x * y⁻¹ = x⁻¹)
    (hgen : Subgroup.closure {x, y} = ⊤) :
    Ihara.HasTrivialSchurMultiplier G := by p2m_exact_reverting @_root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_of_dicyclic.solution
