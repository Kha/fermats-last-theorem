import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_CartierDual_dualBaseChangeLin_bijective_integral

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.dualBaseChangeLin_bijective_integral.{u, v, w}
    (O : Type u) [CommRing O] (O' : Type v) [CommRing O'] [Algebra O O']
    (A : Type w) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A] :
    Function.Bijective (CartierDual.dualBaseChangeLin O O' A) ∧
    CartierDual.dualBaseChangeLin O O' A 1 = 1 ∧
    (∀ x y : O' ⊗[O] CartierDual O A,
        CartierDual.dualBaseChangeLin O O' A (x * y)
          = CartierDual.dualBaseChangeLin O O' A x * CartierDual.dualBaseChangeLin O O' A y) ∧
    (∀ w : O' ⊗[O] CartierDual O A,
        TensorProduct.map (CartierDual.dualBaseChangeLin O O' A) (CartierDual.dualBaseChangeLin O O' A)
            (Coalgebra.comul (R := O') w)
          = Coalgebra.comul (R := O') (CartierDual.dualBaseChangeLin O O' A w)) ∧
    (∀ (g : CartierDual O A) (x : O' ⊗[O] A),
        CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) x
          = CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] g) (HopfAlgebraStruct.antipode (R := O') x)) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_dualBaseChangeLin_bijective_integral.solution
