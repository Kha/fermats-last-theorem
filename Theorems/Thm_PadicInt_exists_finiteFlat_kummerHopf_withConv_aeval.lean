import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_PadicInt_exists_finiteFlat_kummerHopf_withConv_aeval
attribute [-instance] PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA

open scoped NNReal
theorem PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval
    (p : ℕ) [Fact p.Prime] (u : ℚ_[p]) (hu : ‖u‖₊ = 1)
    (ζ η : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ p)
    (hη : η ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) u) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ ψ : (ZMod p × ZMod p) ≃ WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
        ∃ F : H → ZMod p → Polynomial ℤ_[p],
          ∀ (i j : ZMod p) (h : H),
            (ψ (i, j)) h
              = Polynomial.aeval (ζ ^ i.val * η ^ j.val) (F h j) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_finiteFlat_kummerHopf_withConv_aeval.solution
