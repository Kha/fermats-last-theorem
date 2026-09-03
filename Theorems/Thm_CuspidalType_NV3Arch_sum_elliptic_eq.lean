import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_NV3Arch_sum_elliptic_eq

set_option autoImplicit false
open Polynomial CuspidalType in
open scoped Classical in

theorem CuspidalType.NV3Arch.sum_elliptic_eq (q : ℕ) [Fact q.Prime]
    [Fintype (GaloisField q 2)ˣ] {K : Type*} [CommRing K] (F : GL2 q → K)
    (hF : ∀ g h : GL2 q, F (h * g * h⁻¹) = F g) :
    (2 * (q ^ 2 - 1 : ℕ) : K) *
        ∑ g ∈ Finset.univ.filter
          (fun g : GL2 q => ∀ x : ZMod q, ¬ (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x), F g =
      (Nat.card (GL2 q) : K) *
        ∑ α ∈ Finset.univ.filter
          (fun α : (GaloisField q 2)ˣ => (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))),
          F (torus q α) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_NV3Arch_sum_elliptic_eq.solution
