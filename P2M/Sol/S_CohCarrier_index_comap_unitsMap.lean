import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import P2M.Util
namespace P2MW.S_CohCarrier_index_comap_unitsMap

set_option autoImplicit false

theorem solution
    {M M' : ℕ} [NeZero M'] (hMM' : M ∣ M') (H₀ : Subgroup (ZMod M)ˣ) :
    (H₀.comap (ZMod.unitsMap hMM')).index = H₀.index :=
  Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hMM')
