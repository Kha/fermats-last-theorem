import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem

theorem HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem
    {G : Type*} [Group G] {n : ℕ} {U : Subgroup G} {gv : G}
    {reps reps' : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps)
    (hsys' : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps')
    {φ : G → ℂ} (hinv : ∀ g : G, ∀ u ∈ U, φ (g * u) = φ g) (g : G) :
    ∑ i, φ (g * reps' i) = ∑ i, φ (g * reps i) := by p2m_exact_reverting @_root_.P2MW.S_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem.solution
