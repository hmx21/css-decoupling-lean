import Decoupling.HighDim.GluedDirectionalHomotopy

/-!
# Explicit residues in the directional coarse cell

Every original lattice site has a unique integer coarse-cell coordinate
and a row r in {0,...,p-1}. Integer Euclidean division includes sites with
negative coordinates. These are the physical species used by the example's
no-ancilla circuit, not a chosen arbitrary module basis.
-/

namespace Decoupling.HighDim.GluedDirectional

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

def row (r : Fin p) : Translation 3 := (r.val : ℤ) • translationBasis 1

def exponentEquiv : Translation 3 ≃ Fin p × Translation 3 where
  toFun a := (⟨(a 1 % (p : ℤ)).toNat, by
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      have hl := Int.emod_lt_of_pos (a 1) hp
      have hn := Int.emod_nonneg (a 1) (ne_of_gt hp)
      omega⟩, ![a 0, a 1 / p, a 2])
  invFun b := inclusion p b.2 + row p b.1
  left_inv a := by
    funext i
    fin_cases i <;> simp [inclusion, row, translationBasis]
    have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [max_eq_left (Int.emod_nonneg _ hp)]
    exact Int.mul_ediv_add_emod (a 1) p
  right_inv b := by
    rcases b with ⟨r, a⟩
    have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hr : (r.val : ℤ) < p := by exact_mod_cast r.isLt
    have hn : (0 : ℤ) ≤ r.val := by omega
    have hm : ((p : ℤ) * a 1 + r.val) % p = r.val := by
      simp [Int.add_emod, Int.emod_eq_of_lt hn hr]
    have hd : ((p : ℤ) * a 1 + r.val) / p = a 1 := by
      rw [Int.add_ediv_of_dvd_left (dvd_mul_right (p : ℤ) (a 1))]
      rw [Int.mul_ediv_cancel_left _ (ne_of_gt hp), Int.ediv_eq_zero_of_lt hn hr, add_zero]
    apply Prod.ext
    · apply Fin.ext
      simpa [inclusion, row, translationBasis] using congrArg Int.toNat hm
    · funext i
      fin_cases i <;> simp [inclusion, row, translationBasis, hd]

@[simp] theorem exponentEquiv_symm (r : Fin p) (a : Translation 3) :
    (exponentEquiv p).symm (r, a) = inclusion p a + row p r := rfl

abbrev scalarModule : ModuleCat (Laurent (ZMod p) 3) :=
  (ModuleCat.restrictScalars (ringMap p)).obj
    (ModuleCat.of (Laurent (ZMod p) 3) (Laurent (ZMod p) 3))

def decomposeAddEquiv : Laurent (ZMod p) 3 ≃+ (Fin p →₀ Laurent (ZMod p) 3) :=
  AddMonoidAlgebra.coeffAddEquiv.trans <|
    (Finsupp.domCongr (exponentEquiv p)).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv AddMonoidAlgebra.coeffAddEquiv.symm

@[simp] theorem decompose_single (a : Translation 3) (c : ZMod p) :
    decomposeAddEquiv p (AddMonoidAlgebra.single a c) =
      Finsupp.single (exponentEquiv p a).1
        (AddMonoidAlgebra.single (exponentEquiv p a).2 c) := by
  simp [decomposeAddEquiv, Finsupp.domCongr]

def assemble : (Fin p →₀ Laurent (ZMod p) 3) →ₗ[Laurent (ZMod p) 3] scalarModule p :=
  Finsupp.linearCombination (Laurent (ZMod p) 3)
    (fun r => (show scalarModule p from monomial (ZMod p) (row p r)))

@[simp] theorem assemble_single (r : Fin p) (s : Laurent (ZMod p) 3) :
    assemble p (Finsupp.single r s) = ringMap p s * monomial (ZMod p) (row p r) := by
  exact Finsupp.linearCombination_single _ _ _

theorem assemble_decompose (f : Laurent (ZMod p) 3) :
    assemble p (decomposeAddEquiv p f) = f := by
  have h : (assemble p).toAddMonoidHom.comp (decomposeAddEquiv p).toAddMonoidHom =
      AddMonoidHom.id (Laurent (ZMod p) 3) := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a c
    change assemble p (decomposeAddEquiv p (AddMonoidAlgebra.single a c)) = _
    rw [decompose_single, assemble_single]
    change KoszulLattice.latticeMap (ZMod p) (inclusion p)
      (AddMonoidAlgebra.single (exponentEquiv p a).2 c) * monomial (ZMod p) (row p (exponentEquiv p a).1) = _
    simp only [KoszulLattice.latticeMap, AddMonoidAlgebra.mapDomainRingHom_apply,
      AddMonoidAlgebra.mapDomain_single, monomial, AddMonoidAlgebra.single_mul_single, mul_one]
    change AddMonoidAlgebra.single ((exponentEquiv p).symm (exponentEquiv p a)) c = _
    rw [Equiv.symm_apply_apply]
    rfl
  exact DFunLike.congr_fun h f

def assemblyEquiv : (Fin p →₀ Laurent (ZMod p) 3) ≃ₗ[Laurent (ZMod p) 3] scalarModule p :=
  LinearEquiv.ofBijective (assemble p) (by
    have he : (assemble p : (Fin p →₀ Laurent (ZMod p) 3) → Laurent (ZMod p) 3) =
        (decomposeAddEquiv p).symm := by
      funext v
      simpa only [(decomposeAddEquiv p).apply_symm_apply] using
        assemble_decompose p ((decomposeAddEquiv p).symm v)
    rw [he]
    exact (decomposeAddEquiv p).symm.bijective)

def rowBasis : Module.Basis (Fin p) (Laurent (ZMod p) 3) (scalarModule p) :=
  Module.Basis.ofRepr (assemblyEquiv p).symm

@[simp] theorem rowBasis_apply (r : Fin p) : rowBasis p r = monomial (ZMod p) (row p r) := by
  change assemble p (Finsupp.single r 1) = _
  rw [assemble_single, map_one, one_mul]

def rowCoordinates : scalarModule p ≃ₗ[Laurent (ZMod p) 3] (Fin p → Laurent (ZMod p) 3) :=
  (rowBasis p).equivFun

@[simp] theorem rowCoordinates_basis (r : Fin p) :
    rowCoordinates p (monomial (ZMod p) (row p r)) = Pi.single r 1 := by
  rw [← rowBasis_apply]
  funext s
  simpa [rowCoordinates, Pi.single_apply, eq_comm] using (rowBasis p).equivFun_self r s

theorem rowCoordinates_eq_decompose (f : Laurent (ZMod p) 3) (r : Fin p) :
    rowCoordinates p f r = decomposeAddEquiv p f r := by
  have he : (assemblyEquiv p).symm f = decomposeAddEquiv p f := by
    apply (assemblyEquiv p).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (assemble_decompose p f).symm
  exact congrArg (fun v : Fin p →₀ Laurent (ZMod p) 3 => v r) he

@[simp] theorem rowCoordinates_coeff (f : Laurent (ZMod p) 3) (r : Fin p) (a : Translation 3) :
    (rowCoordinates p f r).coeff a = f.coeff (inclusion p a + row p r) := by
  rw [rowCoordinates_eq_decompose]
  simp [decomposeAddEquiv, Finsupp.domCongr, exponentEquiv_symm]

/-- Actual species and residue-row coordinates of the restricted Pauli modules. -/
def vectorCoordinates (n : ℕ) : restrictedFree p n ≃ₗ[Laurent (ZMod p) 3]
    ((Fin n × Fin p) → Laurent (ZMod p) 3) where
  toFun v i := rowCoordinates p (v i.1) i.2
  invFun v i := (rowCoordinates p).symm (fun r => v (i, r))
  left_inv v := by funext i; exact (rowCoordinates p).symm_apply_apply (v i)
  right_inv v := by
    funext i
    exact congrFun ((rowCoordinates p).apply_symm_apply (fun r => v (i.1, r))) i.2
  map_add' v w := by funext i; exact congrFun ((rowCoordinates p).map_add (v i.1) (w i.1)) i.2
  map_smul' a v := by
    funext i
    exact congrFun ((rowCoordinates p).map_smul a (v i.1)) i.2

theorem vectorCoordinates_single (n : ℕ) (j : Fin n) (r : Fin p) :
    vectorCoordinates p n (Pi.single j (monomial (ZMod p) (row p r))) = Pi.single (j, r) 1 := by
  classical
  funext i
  by_cases h : i.1 = j
  · rcases i with ⟨i, s⟩
    dsimp at h
    subst i
    simp [vectorCoordinates, rowCoordinates_basis, Pi.single_apply]
  · simp [vectorCoordinates, h, Prod.ext_iff]

theorem vectorCoordinates_symm_single (n : ℕ) (j : Fin n) (r : Fin p) :
    (vectorCoordinates p n).symm (Pi.single (j, r) 1) =
      Pi.single j (monomial (ZMod p) (row p r)) := by
  apply (vectorCoordinates p n).injective
  rw [LinearEquiv.apply_symm_apply, vectorCoordinates_single]

end
end Decoupling.HighDim.GluedDirectional
