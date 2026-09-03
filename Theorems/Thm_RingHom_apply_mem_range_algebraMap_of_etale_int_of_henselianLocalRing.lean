import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_RingHom_apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing

set_option autoImplicit false

open IsLocalRing

theorem RingHom.apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    (E : Type) [CommRing E] [Algebra.Etale ℤ E]
    (ι : E →+* AlgebraicClosure ℚ) (hι : ∀ e : E, ι e ∈ Pl)
    (φ₀ : E →+* ZMod p) (hφ₀ : ∀ (e : E) (n : ℤ), (n : ZMod p) = φ₀ e → Pl.valuation (ι e - n) < 1) :
    ∀ e : E, ι e ∈ Set.range (algebraMap Rh (AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing.solution
