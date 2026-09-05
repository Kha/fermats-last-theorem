module

public import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_prePsi_eq_expand

@[expose] public section

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.exists_prePsi_eq_expand {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (W : WeierstrassCurve R) : ∃ g : Polynomial R, W.preΨ' p = Polynomial.expand R p g := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.solution
