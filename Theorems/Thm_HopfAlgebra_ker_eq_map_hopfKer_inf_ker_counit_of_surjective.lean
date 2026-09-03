import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.ker_eq_map_hopfKer_inf_ker_counit_of_surjective
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {A : Type} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Flat R A] [Coalgebra.IsCocomm R A]
    {B : Type} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Flat R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    RingHom.ker (π : A →+* B) =
      Ideal.span ((HopfAlgebra.hopfKer π : Set A) ∩ (RingHom.ker (Bialgebra.counitAlgHom R A) : Set A)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective.solution
