import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_HeckeProj
import P2M.Util
import P2M.Sol.S_CuspForm_exists_ringHom_zmod_of_eisenstein_injective

open ModularCurve

theorem CuspForm.exists_ringHom_zmod_of_eisenstein_injective (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hinj : ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈ Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔ Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c) : ∃ χ : CuspForm.heckeAlgebra p 2 ∅ →+* ZMod m, (∀ i ∈ Ideal.map (heckeProj p) (eisensteinIdeal p), χ i = 0) ∧ ∀ c : ℤ, χ (algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c) = (c : ZMod m) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_ringHom_zmod_of_eisenstein_injective.solution
