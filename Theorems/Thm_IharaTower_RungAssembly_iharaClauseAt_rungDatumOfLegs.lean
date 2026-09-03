import Definitions.Def_HeckeModule_IharaRungDatum
import P2M.Util
import P2M.Sol.S_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs

set_option autoImplicit false

open IharaTower in

theorem IharaTower.RungAssembly.iharaClauseAt_rungDatumOfLegs
    {𝒪 : Type} [CommRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}
    {n : ℕ} (L : RungAssembly.LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) (πT : T →ₐ[𝒪] 𝒪)
    (hequiv : ∀ (t' : T') (m : M),
      (RungAssembly.rungDatumOfLegs L c res).i (res t' • m)
        = t' • (RungAssembly.rungDatumOfLegs L c res).i m)
    (hsurj : ∀ w' ∈ (Submodule.torsionBySet T' M'
        ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪,
      ∃ m ∈ (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪,
        (RungAssembly.rungDatumOfLegs L c res).i m = w') :
    IharaClauseAt (RungAssembly.rungDatumOfLegs L c res) πT (πT.comp res) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs.solution
