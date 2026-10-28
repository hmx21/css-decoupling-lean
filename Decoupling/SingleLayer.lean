import Decoupling.DecouplingFromSplitting

/-!
# The vanishing-layer cases of Proposition III.4

The module decompositions are constructed from the actual quotient cochain.
The target matrices are then reindexed by explicit removal of empty species;
the free `h` summand occurs only among the degree-zero labels.  No positive
rank hypotheses are used.  The final specializations construct the existing
stabilization and CNOT certificates with the vanished species set to zero.
-/

namespace Decoupling.SingleLayer

open CategoryTheory CategoryTheory.Abelian EvaluationLinear StandardTarget

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512

variable {q s k : ℕ}
variable (c : Syndrome.Cochain R (Fin q → R) (Fin s → R) (Fin k → R))

/-- A zero second layer makes the actual map `γ` onto. -/
theorem γ_surjective [Subsingleton c.C2] : Function.Surjective c.γ := by
  intro v
  have hv : c.pQ v = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).mp hv

/-- The image is the whole free cover when the second layer vanishes. -/
def imageEquivCover [Subsingleton c.C2] : c.L ≃ₗ[R] (Fin k → R) :=
  LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr (γ_surjective c))

/-- The first displayed module isomorphism in Proposition III.4. -/
def syndromeEquivFirst [Subsingleton c.C2] : c.N ≃ₗ[R] (c.C1 × (Fin k → R)) :=
  (c.equivProdOfκZero (SplitAssembly.κ_zero_of_second_layer_zero c)).trans
    ((LinearEquiv.refl R c.C1).prodCongr (imageEquivCover c))

/-- Vanishing of the first layer makes the actual projection injective. -/
theorem π_injective [Subsingleton c.C1] : Function.Injective c.π := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  obtain ⟨e, he⟩ := c.first.moduleCat_exact_iff.mp c.first_shortExact.exact v hv
  have he0 : (e : c.C1) = 0 := (inferInstance : Subsingleton c.C1).allEq e 0
  simpa only [he0, map_zero] using he.symm

/-- The projection itself is the isomorphism, with no chosen splitting. -/
def projectionEquiv [Subsingleton c.C1] : c.N ≃ₗ[R] c.L :=
  LinearEquiv.ofBijective c.π ⟨π_injective c, c.π_surjective⟩

@[simp] theorem projectionEquiv_apply [Subsingleton c.C1] (n : c.N) :
    projectionEquiv c n = c.π n := rfl

/-- The second displayed module isomorphism, using the proved normalization. -/
def syndromeEquivSecond {t₂ : ℕ} [Subsingleton c.C1]
    (e₂ : c.C2 ≃ₗ[R] Trivial t₂) :
    c.N ≃ₗ[R] ((Fin (k - t₂) → R) × (Fin t₂ → J)) :=
  (projectionEquiv c).trans (ExplicitSplitting.imageNormalization c e₂)

/-- With both layers zero the syndrome is the original free cover. -/
def syndromeEquivFree [Subsingleton c.C1] [Subsingleton c.C2] :
    c.N ≃ₗ[R] (Fin k → R) :=
  (projectionEquiv c).trans (imageEquivCover c)

/-- Every genuine degree-two extension class vanishes if its target is zero. -/
theorem ext_two_eq_zero_of_first [Subsingleton c.C1]
    (e : Ext (ModuleCat.of R c.C2) (ModuleCat.of R c.C1) 2) : e = 0 := by
  have hid : 𝟙 (ModuleCat.of R c.C1) = 0 := by
    apply ModuleCat.hom_ext
    ext v
    exact Subsingleton.elim _ _
  have he := Ext.comp_mk₀_id e
  rw [hid, Ext.mk₀_zero, Ext.comp_zero] at he
  exact he.symm

/-- Every genuine degree-two extension class vanishes if its source is zero. -/
theorem ext_two_eq_zero_of_second [Subsingleton c.C2]
    (e : Ext (ModuleCat.of R c.C2) (ModuleCat.of R c.C1) 2) : e = 0 := by
  have hid : 𝟙 (ModuleCat.of R c.C2) = 0 := by
    apply ModuleCat.hom_ext
    ext v
    exact Subsingleton.elim _ _
  have he := Ext.mk₀_id_comp e
  rw [hid, Ext.mk₀_zero, Ext.zero_comp] at he
  exact he.symm

/-- Remove the empty second species from degree-zero labels. -/
def firstLabels (t h : ℕ) : I₀ t h 0 ≃ (Fin t ⊕ Fin h) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumEmpty _ _)

/-- Remove the empty second species from physical qubits. -/
def firstQubits (t : ℕ) : I₁ t 0 ≃ (Fin 3 × Fin t) := Equiv.sumEmpty _ _

def firstRelations (t : ℕ) : I₂ t 0 ≃ (Fin 3 × Fin t) := Equiv.sumEmpty _ _

/-- Remove the empty first species from degree-zero labels. -/
def secondLabels (h t : ℕ) : I₀ 0 h t ≃ (Fin h ⊕ (Fin 3 × Fin t)) :=
  Equiv.emptySum _ _

/-- Remove the empty first species from physical qubits. -/
def secondQubits (t : ℕ) : I₁ 0 t ≃ (Fin 3 × Fin t) := Equiv.emptySum _ _

def secondRelations (t : ℕ) : I₂ 0 t ≃ Fin t := Equiv.emptySum _ _

/-- The actual first-species matrix is `(∂₁^(t),0)ᵀ` in the printed order. -/
theorem first_D₁ (t h : ℕ) :
    Matrix.reindex (firstLabels t h) (firstQubits t) (D₁ t h 0) =
      Matrix.fromRows (fun j (p : Fin 3 × Fin t) =>
        if j = p.2 then PhysicalKoszul.partial₁ 0 p.1 else 0) 0 := by
  apply Matrix.ext
  intro row col
  rcases row with j | j
  · exact D₁_first_block t h 0 j col.2 col.1
  · exact D₁_free_row t h 0 j (.inl col)

/-- The first-species physical boundary is `∂₂ ⊗ Iₜ`. -/
theorem first_D₂ (t : ℕ) :
    Matrix.reindex (firstQubits t) (firstRelations t) (D₂ t 0) =
      (fun (p r : Fin 3 × Fin t) =>
        if p.2 = r.2 then PhysicalKoszul.partial₂ p.1 r.1 else 0) := by
  apply Matrix.ext
  intro row col
  exact D₂_first_block t 0 row.1 col.1 row.2 col.2

/-- The actual second-species matrix is `(0,∂₂^(t))ᵀ` in the printed order. -/
theorem second_D₁ (h t : ℕ) :
    Matrix.reindex (secondLabels h t) (secondQubits t) (D₁ 0 h t) =
      Matrix.fromRows 0 (fun (p r : Fin 3 × Fin t) =>
        if p.2 = r.2 then PhysicalKoszul.partial₂ p.1 r.1 else 0) := by
  apply Matrix.ext
  intro row col
  rcases row with j | j
  · exact D₁_free_row 0 h t j (.inr col)
  · exact D₁_second_block 0 h t j.1 col.1 j.2 col.2

/-- The second-species physical boundary is `∂₃ ⊗ Iₜ`. -/
theorem second_D₂ (t : ℕ) :
    Matrix.reindex (secondQubits t) (secondRelations t) (D₂ 0 t) =
      (fun (p : Fin 3 × Fin t) j =>
        if p.2 = j then PhysicalKoszul.partial₃ p.1 0 else 0) := by
  apply Matrix.ext
  intro row col
  exact D₂_second_block 0 t row.1 row.2 col

/-- The correction term is literally empty when the first layer is absent. -/
theorem correctedMatrix_zero_layer {s n : ℕ}
    (T : Matrix (Fin s) (Fin 0) R) (C : Matrix (Fin 0) (Fin s) (ZMod 2))
    (V : Matrix (Fin s) (Fin n) R) :
    ExplicitSplitting.correctedMatrix T C V = V := by
  apply Matrix.ext
  intro i j
  simp [ExplicitSplitting.correctedMatrix]

/-- There are no toric physical coordinates when both layers vanish. -/
theorem target_qubits_zero : Fintype.card (I₁ 0 0) = 0 := by
  simp [I₁]

section ActualLayers

local instance : Subsingleton (Trivial 0) :=
  inferInstanceAs (Subsingleton (Fin 0 → ZMod 2))

variable {r cX t₁ t₂ : ℕ} {checks : CSS.Checks q s r}
variable (resolution : ResolutionExt.CSSResolution checks cX)

/-- The first isomorphism with the actual derived Ext layer as endpoint. -/
def syndromeEquivFirstActual [Subsingleton (ExtLayers.E_X checks 2)] :
    checks.N ≃ₗ[R] (ExtLayers.E_X checks 1 × (Fin cX → R)) := by
  let : Subsingleton resolution.cochain.C2 :=
    resolution.C2EquivE_X.injective.subsingleton
  exact (syndromeEquivFirst resolution.cochain).trans
    (resolution.C1EquivE_X.prodCongr (LinearEquiv.refl R _))

/-- The second isomorphism with vanishing of the actual first Ext layer. -/
def syndromeEquivSecondActual [Subsingleton (ExtLayers.E_X checks 1)]
    (e₂ : ExtLayers.E_X checks 2 ≃ₗ[R] Trivial t₂) :
    checks.N ≃ₗ[R] ((Fin (cX - t₂) → R) × (Fin t₂ → J)) := by
  let : Subsingleton resolution.cochain.C1 :=
    resolution.C1EquivE_X.injective.subsingleton
  exact syndromeEquivSecond resolution.cochain (resolution.C2EquivE_X.trans e₂)

include resolution in
/-- The actual splitting, stabilization, image and CNOT certificates with only
the first toric species.  Vanishing of the second layer supplies `κ=0`. -/
theorem exists_first_certificate (hTop : checks.Topological)
    [Subsingleton (ExtLayers.E_X checks 2)]
    (e₁ : Trivial t₁ ≃ₗ[R] ExtLayers.E_X checks 1) :
    Nonempty (DecouplingFromSplitting.Certificate checks cX t₁ 0) := by
  let : Subsingleton resolution.cochain.C2 :=
    resolution.C2EquivE_X.injective.subsingleton
  exact DecouplingFromSplitting.exists_certificate hTop resolution
    (e₁.trans resolution.C1EquivE_X.symm)
    (LinearEquiv.ofSubsingleton _ _)
    (SplitAssembly.κ_zero_of_second_layer_zero resolution.cochain)

include resolution in
/-- The corresponding certificate with only the second toric species. -/
theorem exists_second_certificate (hTop : checks.Topological)
    [Subsingleton (ExtLayers.E_X checks 1)]
    (e₂ : ExtLayers.E_X checks 2 ≃ₗ[R] Trivial t₂) :
    Nonempty (DecouplingFromSplitting.Certificate checks cX 0 t₂) := by
  let : Subsingleton resolution.cochain.C1 :=
    resolution.C1EquivE_X.injective.subsingleton
  exact DecouplingFromSplitting.exists_certificate hTop resolution
    (LinearEquiv.ofSubsingleton _ _) (resolution.C2EquivE_X.trans e₂)
    (SplitAssembly.κ_zero_of_first_layer_zero resolution.cochain)

include resolution in
/-- Both actual Ext layers vanish: the constructed target has only the
product-state blocks, since its toric physical index `I₁ 0 0` is empty. -/
theorem exists_product_certificate (hTop : checks.Topological)
    [Subsingleton (ExtLayers.E_X checks 1)] [Subsingleton (ExtLayers.E_X checks 2)] :
    Nonempty (DecouplingFromSplitting.Certificate checks cX 0 0) :=
  exists_first_certificate resolution hTop (LinearEquiv.ofSubsingleton _ _)

end ActualLayers

section ProductTarget

open DecouplingFromSplitting

/-- The nonempty output physical coordinates consist of the X and Z ancillary
blocks only, in that order.  Degree-zero free labels stay in the Z block. -/
def productCoordinates (q s k : ℕ) :
    Target q s k 0 0 ≃ (Fin s ⊕ (Fin q ⊕ Target₀ k 0 0)) :=
  Equiv.sumCongr (Equiv.emptySum _ _) (Equiv.refl _)

/-- With both layers zero the actual stabilized X matrix is an identity
on the X ancillary block and zero on every other physical coordinate. -/
theorem product_X (d : Comparison q s k 0 0) :
    Matrix.reindex (Equiv.refl _) (productCoordinates q s k) d.H_X_tilde =
      Matrix.fromBlocks
        (0 : Matrix (Target₀ k 0 0) (Fin s) R)
        (0 : Matrix (Target₀ k 0 0) (Fin q ⊕ Target₀ k 0 0) R)
        (1 : Matrix (Fin s) (Fin s) R) 0 := by
  apply Matrix.ext
  intro row col
  rcases row with i | i <;> rcases col with j | j <;> rfl

/-- The stabilized Z matrix is an identity on the other ancillary block,
after removing its empty toric generator species. -/
theorem product_Z :
    Matrix.reindex (productCoordinates q s k) (Equiv.emptySum _ _)
      (targetZ (q := q) (s := s) k 0 0) =
      Matrix.fromRows (0 : Matrix (Fin s) (Fin q ⊕ Target₀ k 0 0) R) 1 := by
  apply Matrix.ext
  intro row col
  rcases row with i | i <;> rfl

end ProductTarget

end
end Decoupling.SingleLayer
