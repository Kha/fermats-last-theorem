module

public import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_prePsi_ne_zero_of_isElliptic

@[expose] public section

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.prePsi_ne_zero_of_isElliptic {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : Odd n) : W.preΨ' n ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_prePsi_ne_zero_of_isElliptic.solution
