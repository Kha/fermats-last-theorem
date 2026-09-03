import Mathlib
import P2M.Util
import P2M.Sol.S_TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization

set_option autoImplicit false

universe u

theorem TopologicalSpace.NoetherianSpace.isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {s : Set X}
    (h₁ : StableUnderSpecialization s) (h₂ : StableUnderGeneralization s) : IsClopen s := by p2m_exact_reverting @_root_.P2MW.S_TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization.solution
