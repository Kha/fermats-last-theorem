module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant

@[expose] public section

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.coeff_prePsi_eq_hasseInvariant {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) [CharP R p] (W : WeierstrassCurve R) : (W.preΨ' p).coeff (p * ((p - 1) / 2)) = W.hasseInvariant p := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_coeff_prePsi_eq_hasseInvariant.solution
