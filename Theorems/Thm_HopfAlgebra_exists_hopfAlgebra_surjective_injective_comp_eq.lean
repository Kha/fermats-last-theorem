import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq

universe u v

theorem HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ : H →ₐc[R] H') :
    ∃ (Q : Type v) (_ : CommRing Q) (_ : HopfAlgebra R Q) (_ : Module.Finite R Q) (_ : Module.Flat R Q)
      (π : H →ₐc[R] Q) (ι : Q →ₐc[R] H'),
      Function.Surjective π ∧ Function.Injective ι ∧ ι.comp π = φ := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.solution
