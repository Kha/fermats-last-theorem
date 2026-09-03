import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing

set_option autoImplicit false

universe u v w

theorem WittVector.bijective_sum_map_mul_teichmuller_basis_of_perfectRing
    (p : ℕ) [Fact p.Prime] {k : Type u} {l : Type v} [CommRing k] [CommRing l]
    [CharP k p] [CharP l p] [PerfectRing k p] [PerfectRing l p] [Algebra k l]
    {ι : Type w} [Fintype ι] (b : Module.Basis ι k l) :
    Function.Bijective fun a : ι → WittVector p k =>
      ∑ i, WittVector.map (algebraMap k l) (a i) * WittVector.teichmuller p (b i) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing.solution
