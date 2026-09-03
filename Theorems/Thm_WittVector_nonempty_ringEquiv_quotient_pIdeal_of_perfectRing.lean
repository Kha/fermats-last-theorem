import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Nonempty (k ≃+* (WittVector p k ⧸ pIdeal p (WittVector p k))) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing.solution
