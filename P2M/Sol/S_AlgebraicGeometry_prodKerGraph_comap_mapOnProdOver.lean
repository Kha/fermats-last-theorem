import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme IsSeparated Scheme.IdealSheafData prodKerGraph prodKerGraph_eq_prod graphOver RelEffCartierDiv mapOnProdOver RelEffCartierDiv.I RelEffCartierDiv.pullbackAlong_ofPoint Scheme.IdealSheafData.comap_mul"
namespace ProdKerGraphNaturality
p2m_open "AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
  {g' : T' ⟶ S}

theorem ker_graphOver_comap (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (graphOver f a ha).ker.comap (mapOnProdOver f φ hφ) =
      (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).ker :=
  congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint f a ha φ hφ)

omit [IsSeparated f] in

theorem comap_finsetProd {ι : Type*} (s : Finset ι)
    (I : ι → (pullback f g').IdealSheafData) (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (∏ i ∈ s, I i).comap (mapOnProdOver f φ hφ) = ∏ i ∈ s, (I i).comap (mapOnProdOver f φ hφ) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Scheme.IdealSheafData.comap_mul, ih]

theorem prodKerGraph_comap {r : ℕ} (a : Fin r → (T' ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g')
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f φ hφ) =
      prodKerGraph f (fun i => φ ≫ a i) (fun i => by rw [Category.assoc, ha, hφ]) := by
  simp only [prodKerGraph_eq_prod, comap_finsetProd, ker_graphOver_comap]

end AlgebraicGeometry.ProdKerGraphNaturality

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : Fin r → (T' ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g') (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f φ hφ) =
      prodKerGraph f (fun i => φ ≫ a i) (fun i => by rw [Category.assoc, ha, hφ]) :=
  AlgebraicGeometry.ProdKerGraphNaturality.prodKerGraph_comap a ha φ hφ
