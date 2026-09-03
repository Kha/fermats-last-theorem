import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_Eisenstein
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinKernelKillsCuspidalClass_heckeModuleBar

open ModularCurve AlgebraicCurve
theorem ModularCurve.eisensteinKernelKillsCuspidalClass_heckeModuleBar (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (hT : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → heckeOperatorBar p ℓ (cuspidalClass p) = (1 + ℓ : ℤ) • cuspidalClass p) (hU : heckeOperatorBar p ⟨p, Fact.out⟩ (cuspidalClass p) = cuspidalClass p) : EisensteinKernelKillsCuspidalClass p (heckeModuleBar p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinKernelKillsCuspidalClass_heckeModuleBar.solution
