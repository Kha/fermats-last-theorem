import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FreyPackage_ExchangeCase
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_FreyPackage_GaloisRep
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_RibetLevelLowering_CharacterGroupApparatusV2
import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_FreyPackage_AtPNewLowering

open WeierstrassCurve WeierstrassCurve.Affine.Point

set_option autoImplicit false

noncomputable section

namespace FreyPackage

noncomputable local instance instDecEqQbarDescentRepoint :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def MazurPrincipleNewLoweringAt (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    ¬ P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevelAt N

def ExchangeCaseLoweringAt (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevelAt N

def AtPNewLoweringAt (P : FreyPackage) : Prop :=
  ∀ N₀ : ℕ, 0 < N₀ → ¬ P.p ∣ N₀ →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.freyCurve.IsPeuRamifieeAt P.p P.p →
    P.ModularRepOfLevelNewAt (N₀ * P.p) P.p →
    P.ModularRepOfLevelAt N₀

end FreyPackage

end
