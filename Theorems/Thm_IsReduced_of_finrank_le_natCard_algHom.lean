import Mathlib
import P2M.Util
import P2M.Sol.S_IsReduced_of_finrank_le_natCard_algHom

theorem IsReduced.of_finrank_le_natCard_algHom (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B] (h : Module.finrank K B ≤ Nat.card (B →ₐ[K] K)) : IsReduced B := by p2m_exact_reverting @_root_.P2MW.S_IsReduced_of_finrank_le_natCard_algHom.solution
