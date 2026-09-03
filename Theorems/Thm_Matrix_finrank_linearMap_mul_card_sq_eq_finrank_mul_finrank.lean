import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank

set_option autoImplicit false

universe u v w w'

theorem Matrix.finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank
    (k : Type u) [Field k] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (V : Type w) (W : Type w') [AddCommGroup V] [Module k V] [Module (Matrix ι ι k) V]
    [IsScalarTower k (Matrix ι ι k) V]
    [AddCommGroup W] [Module k W] [Module (Matrix ι ι k) W] [IsScalarTower k (Matrix ι ι k) W]
    [FiniteDimensional k V] [FiniteDimensional k W] :
    Module.finrank k (V →ₗ[Matrix ι ι k] W) * Fintype.card ι ^ 2 =
      Module.finrank k V * Module.finrank k W := by p2m_exact_reverting @_root_.P2MW.S_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank.solution
