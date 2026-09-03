import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Basic
import P2M.Util
import P2M.Sol.S_FinFlatHopf_exists_left_integral_frobenius

theorem FinFlatHopf.exists_left_integral_frobenius
    (B : Type) [CommRing B] [IsLocalRing B]
    (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Free B H] [Module.Finite B H] :
    ∃ l : WithConv (H →ₗ[B] B),
      (∀ f : WithConv (H →ₗ[B] B), f * l = f 1 • l) ∧
      Function.Bijective (fun h : H =>
        WithConv.toConv (l.ofConv ∘ₗ LinearMap.mulRight B (HopfAlgebra.antipode B h))) := by p2m_exact_reverting @_root_.P2MW.S_FinFlatHopf_exists_left_integral_frobenius.solution
