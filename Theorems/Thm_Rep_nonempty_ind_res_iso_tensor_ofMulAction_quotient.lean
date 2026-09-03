import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_ind_res_iso_tensor_ofMulAction_quotient
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.nonempty_ind_res_iso_tensor_ofMulAction_quotient
    {k : Type} [CommRing k] {G : Type} [Group G] (D : Subgroup G) (M : Rep.{0} k G) :
    Nonempty (Rep.ind D.subtype (Rep.res D.subtype M) ≅ M ⊗ Rep.ofMulActionFinsupp k G (G ⧸ D)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_ind_res_iso_tensor_ofMulAction_quotient.solution
