import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective
    {R : Type} [CommRing R] [IsLocalRing R]
    {A C : Type} [CommRing A] [CommRing C] [HopfAlgebra R A] [HopfAlgebra R C]
    [Module.Finite R A] [Module.Free R A] [Module.Finite R C] [Module.Free R C]
    (π : A →ₐc[R] C) (hπ : Function.Surjective π) :
    (Subalgebra.toSubmodule (HopfAlgebra.hopfKer π)).baseChange (IsLocalRing.ResidueField R) =
      Subalgebra.toSubmodule (HopfAlgebra.hopfKer
        (Bialgebra.TensorProduct.map
          (BialgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) π)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_baseChange_toSubmodule_hopfKer_eq_toSubmodule_hopfKer_map_residueField_of_surjective.solution
