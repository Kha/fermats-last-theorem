import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import P2M.Util
import P2M.Sol.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open Polynomial ModularCurve ModularCurve.HpoolLevelRing
open scoped TensorProduct

theorem ModularCurve.HpoolLevelRing.etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient
    (p : ℕ) [Fact p.Prime] [NeZero p] (f : ℤ) (u : Afin p) (g : ℤ[X])
    (P : Ideal (Localization.Away f)) [P.IsPrime]
    (k : Type) [Field k] [Algebra k P.ResidueField] :
    (Algebra.Etale k ((k ⊗[ℤ] Afin p) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] Polynomial.aeval u g}) →
        Algebra.Etale P.ResidueField (P.Fiber (levelRing p f u g))) ∧
    Module.finrank P.ResidueField (P.Fiber (levelRing p f u g)) =
      Module.finrank k ((k ⊗[ℤ] Afin p) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] Polynomial.aeval u g}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient.solution
