import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_lawIso_of_forall_isBaseChange_mk_pow

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.exists_lawIso_of_forall_isBaseChange_mk_pow
    {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (F' F : FormalGroup R)
    (F'q Fq : ∀ n : ℕ, FormalGroup (R ⧸ maximalIdeal R ^ (n + 1)))
    (hF' : ∀ n : ℕ, F'.IsBaseChange (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) (F'q n))
    (hF : ∀ n : ℕ, F.IsBaseChange (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) (Fq n))
    (ψ : ∀ n : ℕ, FormalGroup.LawIso (F'q n) (Fq n))
    (hψ : ∀ n : ℕ, PowerSeries.map (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1)))
      (ψ (n + 1)).series = (ψ n).series) :
    ∃ Ψ : FormalGroup.LawIso F' F, ∀ n : ℕ,
      PowerSeries.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) Ψ.series = (ψ n).series := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_lawIso_of_forall_isBaseChange_mk_pow.solution
