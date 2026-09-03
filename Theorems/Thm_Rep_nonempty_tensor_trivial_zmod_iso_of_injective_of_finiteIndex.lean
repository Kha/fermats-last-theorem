import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    (L L' : Rep ℤ G) [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L']
    (f : L ⟶ L') (hf : Function.Injective f.hom) (hfi : (f.hom : L →+ L').range.FiniteIndex) :
    Nonempty (L ⊗ Rep.trivial ℤ G (ZMod p) ≅ L' ⊗ Rep.trivial ℤ G (ZMod p)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex.solution
