import Mathlib
import P2M.Util
import P2M.Sol.S_exists_spanningTree_of_connected

theorem exists_spanningTree_of_connected {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (hd tl : E → V)
    (hconn : ∀ u v : V, ∃ c : E → ℤ,
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) :
    ∃ T : Finset E, ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_exists_spanningTree_of_connected.solution
