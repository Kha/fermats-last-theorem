import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.finrank_hom_eq_add_of_shortExact_of_card_coprime
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H] (hH : (Nat.card H).Coprime p)
    (T : Rep.{0} (ZMod p) H) [FiniteDimensional (ZMod p) T]
    (X : ShortComplex (Rep.{0} (ZMod p) H)) (hX : X.ShortExact) [FiniteDimensional (ZMod p) X.X₂] :
    Module.finrank (ZMod p) (T ⟶ X.X₂) =
      Module.finrank (ZMod p) (T ⟶ X.X₁) + Module.finrank (ZMod p) (T ⟶ X.X₃) := by p2m_exact_reverting @_root_.P2MW.S_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime.solution
