import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
attribute [-simp] AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow
    {𝒞 S T T' : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {g : T ⟶ S} {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) [IsAffineHom φ]
    (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    {ι : Type} [Fintype ι] (b : ι → (T' ⟶ 𝒞)) (hb : ∀ i, b i ≫ f = g') (e : ι → ℕ) :
    (RelEffCartierDiv.ofPoint f a ha).I.comap (mapOnProdOver f φ hφ) =
        (RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I ∧
      ((RelEffCartierDiv.ofPoint f a ha).I * ∏ i, (RelEffCartierDiv.ofPoint f (b i) (hb i)).I ^ (e i)).comap
          (mapOnProdOver f φ hφ) =
        (RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I *
          ∏ i, (RelEffCartierDiv.ofPoint f (φ ≫ b i) (by rw [Category.assoc, hb i, hφ])).I ^ (e i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow.solution
