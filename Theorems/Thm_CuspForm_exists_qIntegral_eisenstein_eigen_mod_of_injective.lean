import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_CuspForm_IntegralLattice
import P2M.Util
import P2M.Sol.S_CuspForm_exists_qIntegral_eisenstein_eigen_mod_of_injective

open ModularCurve

theorem CuspForm.exists_qIntegral_eisenstein_eigen_mod_of_injective (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hIB : CuspForm.HasIntegralBasis p) (hinj : ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈ Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔ Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c) : ∃ f ∈ CuspForm.qIntegralSet p, ∃ af : ℕ → ℤ, (∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧ IsCoprime (af 1) (m : ℤ) ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * ℓ) + (if ℓ ∣ n then (ℓ : ℤ) * af (n / ℓ) else 0) - (1 + ℓ) * af n) ∧ (∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * p) - af n) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_qIntegral_eisenstein_eigen_mod_of_injective.solution
