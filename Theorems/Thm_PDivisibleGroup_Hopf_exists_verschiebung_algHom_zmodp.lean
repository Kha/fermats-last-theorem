import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp

universe v

theorem PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp
    (p : ℕ) [Fact p.Prime] (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A]
    [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A] :
    ∃ V : A →ₐc[ZMod p] A,
      (∀ a, (V a) ^ p = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) A p a) ∧
      (∀ a, V (a ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) A p a) ∧
      (∀ (φ : CartierDual (ZMod p) A) (a : A), φ (V a) = (φ ^ p) a) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp.solution
