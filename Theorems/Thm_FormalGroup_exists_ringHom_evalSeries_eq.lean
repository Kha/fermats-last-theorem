import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_ringHom_evalSeries_eq

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.exists_ringHom_evalSeries_eq
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (x : T) (hx : x ∈ I) :
    ∃ e : PowerSeries T →+* T,
      (∀ f : PowerSeries T, (letI : WithIdeal T := ⟨I⟩; FormalGroup.evalSeries f x) = e f) ∧
      (∀ p : Polynomial T, e (p : PowerSeries T) = p.eval x) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_ringHom_evalSeries_eq.solution
