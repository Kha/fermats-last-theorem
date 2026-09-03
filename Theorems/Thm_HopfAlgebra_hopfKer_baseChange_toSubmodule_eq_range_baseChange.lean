import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange
    {R : Type u} [CommRing R] (R₁ : Type u) [CommRing R₁] [Algebra R R₁] [Module.Flat R R₁]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') :
    Subalgebra.toSubmodule
        (HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
          R₁ ⊗[R] H →ₐc[R₁] R₁ ⊗[R] H'))
      = LinearMap.range ((HopfAlgebra.hopfKer qc).val.toLinearMap.baseChange R₁) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange.solution
