import Definitions.Def_CuspForm_ModPForms
import Mathlib.Algebra.Field.ZMod
import P2M.Util
import P2M.Sol.S_ModPForms_mem_modPMod_of_mul_mem_of_forall_zmod
set_option autoImplicit false
theorem ModPForms.mem_modPMod_of_mul_mem_of_forall_zmod (p : ℕ) [Fact p.Prime] (N : ℕ) (k k' k'' : ℤ) (F : Type) [Field F] [CharP F p]
    (P : PowerSeries (ZMod p))
    (h : ∀ ψ : PowerSeries (ZMod p), ψ ∈ ModPForms.modPMod N k (ZMod p) →
      P * ψ ∈ ModPForms.modPMod N k' (ZMod p) → ψ ∈ ModPForms.modPMod N k'' (ZMod p))
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N k F)
    (hP : PowerSeries.map (ZMod.castHom (dvd_refl p) F) P * φ ∈ ModPForms.modPMod N k' F) :
    φ ∈ ModPForms.modPMod N k'' F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_mem_modPMod_of_mul_mem_of_forall_zmod.solution
