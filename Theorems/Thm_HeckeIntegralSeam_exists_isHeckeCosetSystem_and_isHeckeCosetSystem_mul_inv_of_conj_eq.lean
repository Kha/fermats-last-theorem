import Mathlib
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq

set_option autoImplicit false

theorem HeckeIntegralSeam.exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq
    {G : Type*} [Group G] {U : Subgroup G} {g w z : G} {ι : Type*} {reps : ι → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (hw : w ∈ U)
    (hz : z ∈ Subgroup.center G) (hconj : w * g * w⁻¹ = z * g⁻¹) :
    ∃ ε : ι → G, HeckeIntegralSeam.IsHeckeCosetSystem U g ε ∧
      (∀ i, (QuotientGroup.mk (ε i) : G ⧸ U) = QuotientGroup.mk (reps i)) ∧
      HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => z * (ε i)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq.solution
