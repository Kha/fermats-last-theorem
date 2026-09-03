import Mathlib
import P2M.Util
import P2M.Sol.S_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList

universe u

open CategoryTheory CategoryTheory.Limits

theorem RingTheory.Sequence.IsWeaklyRegular.isZero_tor_one_quotient_ofList
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {rs : List R} (hM : RingTheory.Sequence.IsWeaklyRegular M rs) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj
      (ModuleCat.of R M)) := by p2m_exact_reverting @_root_.P2MW.S_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList.solution
