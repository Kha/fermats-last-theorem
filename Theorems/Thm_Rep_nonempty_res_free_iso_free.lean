import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_res_free_iso_free

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_res_free_iso_free {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (α : Type u) :
    ∃ β : Type u, Nonempty (Rep.res S.subtype (Rep.free k G α) ≅ Rep.free k S β) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_res_free_iso_free.solution
