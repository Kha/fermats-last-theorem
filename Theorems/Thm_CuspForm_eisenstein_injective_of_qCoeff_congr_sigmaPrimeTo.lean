import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_CuspForm_IntegralLattice
import P2M.Util
import P2M.Sol.S_CuspForm_eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo

open ModularCurve

theorem CuspForm.eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (hf : f ∈ CuspForm.qIntegralSet p) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (h1 : IsCoprime (af 1) (m : ℤ)) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈ Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔ Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo.solution
