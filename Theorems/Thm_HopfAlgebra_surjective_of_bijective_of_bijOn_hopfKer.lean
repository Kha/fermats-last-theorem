import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer

universe u v w

theorem HopfAlgebra.surjective_of_bijective_of_bijOn_hopfKer
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    {Q : Type w} [CommRing Q] [HopfAlgebra R Q] [Module.Finite R Q] [Module.Flat R Q]
    {Q' : Type w} [CommRing Q'] [HopfAlgebra R Q'] [Module.Finite R Q'] [Module.Flat R Q']
    (φ : H →ₐc[R] H') (π : H →ₐc[R] Q) (π' : H' →ₐc[R] Q') (ψ : Q →ₐc[R] Q')
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (hcomm : (π' : H' →ₐ[R] Q').comp (φ : H →ₐ[R] H') = (ψ : Q →ₐ[R] Q').comp (π : H →ₐ[R] Q))
    (hψ : Function.Bijective ψ)
    (hφ : Set.BijOn φ (HopfAlgebra.hopfKer π) (HopfAlgebra.hopfKer π')) :
    Function.Surjective φ := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_surjective_of_bijective_of_bijOn_hopfKer.solution
