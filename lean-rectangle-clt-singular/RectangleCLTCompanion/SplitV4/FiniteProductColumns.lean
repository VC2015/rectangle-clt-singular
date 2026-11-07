import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Genuine finite-product row/column reindexing, with arbitrary coordinate laws. -/
open MeasureTheory Set
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def finiteProductCells {I J E : Type*} (z : I → J → E) : I × J → E := fun ij => z ij.1 ij.2
def finiteProductRows {I J E : Type*} (z : I × J → E) : I → J → E := fun i j => z (i,j)

theorem finite_product_cells_law {I J E : Type*} [Fintype I] [Fintype J] [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : J => ν))).map finiteProductCells = Measure.pi (fun _ : I × J => ν) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  have hm : Measurable (finiteProductCells (I := I) (J := J) (E := E)) := measurable_pi_lambda _ (fun ij =>
    (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : finiteProductCells ⁻¹' (univ.pi s) = univ.pi (fun i : I => univ.pi (fun j : J => s (i,j))) := by
    ext z
    simp [finiteProductCells]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ij : I × J => ν (s ij))).symm

theorem finite_product_columns_preserving {I J E : Type*} [Fintype I] [Fintype J] [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : I → J → E => fun j i => z i j)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => ν)))
      (Measure.pi (fun _ : J => Measure.pi (fun _ : I => ν))) := by
  have hcells : Measurable (finiteProductCells (I := I) (J := J) (E := E)) :=
    measurable_pi_lambda _ (fun ij => (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))
  have hrows : Measurable (finiteProductRows (I := J) (J := I) (E := E)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun i => measurable_pi_apply (j,i)))
  have hcellsRev : Measurable (finiteProductCells (I := J) (J := I) (E := E)) :=
    measurable_pi_lambda _ (fun ji => (measurable_pi_apply ji.2).comp (measurable_pi_apply ji.1))
  let e := MeasurableEquiv.piCongrLeft (fun _ : J × I => E) (Equiv.prodComm I J)
  have he : MeasurePreserving e (Measure.pi (fun _ : I × J => ν)) (Measure.pi (fun _ : J × I => ν)) :=
    measurePreserving_piCongrLeft (fun _ : J × I => ν) (Equiv.prodComm I J)
  refine ⟨measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun i =>
    (measurable_pi_apply j).comp (measurable_pi_apply i))), ?_⟩
  have hrowlaw : (Measure.pi (fun _ : J × I => ν)).map finiteProductRows = Measure.pi (fun _ : J => Measure.pi (fun _ : I => ν)) := by
    rw [← finite_product_cells_law (I := J) (J := I) ν, Measure.map_map hrows hcellsRev]
    exact Measure.map_id
  calc
    _ = (((Measure.pi (fun _ : I => Measure.pi (fun _ : J => ν))).map finiteProductCells).map e).map finiteProductRows := by
      rw [Measure.map_map he.measurable hcells, Measure.map_map hrows (he.measurable.comp hcells)]
      rfl
    _ = ((Measure.pi (fun _ : I × J => ν)).map e).map finiteProductRows := by rw [finite_product_cells_law]
    _ = _ := by rw [he.map_eq, hrowlaw]

end
end RectangleCLT.Companion.SplitV4
