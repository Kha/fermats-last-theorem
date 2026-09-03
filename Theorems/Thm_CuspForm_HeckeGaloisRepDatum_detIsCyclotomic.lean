import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_CuspForm_HeckeGaloisRepDatum_detIsCyclotomic
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

variable {p : ℕ} {N : ℕ} [NeZero N] {S : Finset ℕ}
  {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
  {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
  [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
theorem CuspForm.HeckeGaloisRepDatum.detIsCyclotomic (hp : p.Prime)
    (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T) :
    H.ρ.DetIsCyclotomic p := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HeckeGaloisRepDatum_detIsCyclotomic.solution
