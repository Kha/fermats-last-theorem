import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
import P2M.Sol.S_ModularCurve_eigenIdeal_isMaximal

theorem ModularCurve.eigenIdeal_isMaximal {k : Type*} [Field k] [Finite k] (a : Nat.Primes → k) : (ModularCurve.eigenIdeal a).IsMaximal := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eigenIdeal_isMaximal.solution
