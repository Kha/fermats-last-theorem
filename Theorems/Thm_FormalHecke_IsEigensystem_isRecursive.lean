import Mathlib
import Definitions.Def_FormalHecke_Eigensystem
import P2M.Util
import P2M.Sol.S_FormalHecke_IsEigensystem_isRecursive

open FormalHecke
theorem FormalHecke.IsEigensystem.isRecursive {R : Type*} [CommRing R] {e a : ℕ → R}
    (h : FormalHecke.IsEigensystem e a) : FormalHecke.IsRecursive e a := by p2m_exact_reverting @_root_.P2MW.S_FormalHecke_IsEigensystem_isRecursive.solution
