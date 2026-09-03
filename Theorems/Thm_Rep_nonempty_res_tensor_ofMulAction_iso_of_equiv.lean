import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_res_tensor_ofMulAction_iso_of_equiv
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.nonempty_res_tensor_ofMulAction_iso_of_equiv
    {k : Type} [CommRing k] {G : Type} [Group G] (C : Subgroup G) (M : Rep.{0} k G)
    {X Y : Type} [MulAction G X] [MulAction G Y]
    (e : X ≃ Y) (he : ∀ (c : C) (x : X), e ((c : G) • x) = (c : G) • e x) :
    Nonempty (Rep.res C.subtype (M ⊗ Rep.ofMulActionFinsupp k G X) ≅ Rep.res C.subtype (M ⊗ Rep.ofMulActionFinsupp k G Y)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_res_tensor_ofMulAction_iso_of_equiv.solution
