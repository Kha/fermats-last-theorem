import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct

open TensorProduct in

theorem Module.Flat.exists_ne_zero_flat_localization_tensorProduct
    {A B M : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧
      Module.Flat A (Localization (Submonoid.powers (algebraMap A B a)) ⊗[B] M) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.solution
