import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hH : E₀.hasseInvariant q = 0) :
    ∃ E₁ : WeierstrassCurve (DualNumber k),
      E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      TrivSqZeroExt.snd (E₁.hasseInvariant q) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero.solution
