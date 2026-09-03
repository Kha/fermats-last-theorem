import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt

universe u

theorem HenselianLocalRing.exists_algHom_lift_of_isSmoothAt
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (φ : S →ₐ[R] IsLocalRing.ResidueField R)
    [(RingHom.ker φ).IsPrime] [Algebra.IsSmoothAt R (RingHom.ker φ)] :
    ∃ ψ : S →ₐ[R] R, ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt.solution
