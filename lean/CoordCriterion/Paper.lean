import CoordCriterion.Paper.S2_FunctionalCALM
import CoordCriterion.Paper.S3_CompleteCALM
import CoordCriterion.Paper.S4_Distributed
import CoordCriterion.Paper.S4_5_CompleteCAP
import CoordCriterion.Paper.S5_Instances
import CoordCriterion.Paper.AppA_Notation
import CoordCriterion.Paper.AppB_Proofs
import CoordCriterion.Paper.AppB_InvariantConfluence
import CoordCriterion.Paper.AppC_CommitmentBases
import CoordCriterion.Paper.AppD_Composition
import CoordCriterion.Paper.AppE_Deployment
import CoordCriterion.Paper.AppF_ResponseAvailability
import CoordCriterion.Paper.AppG_TransactionBases
import CoordCriterion.Paper.AppH_Frontiers
import CoordCriterion.Paper.AppI_Applications

/-!
# The paper, result by result

Each file under `Paper/` follows one section or appendix of the paper, in
paper order.  Every numbered result is a declaration named by its LaTeX label
(for example `CC.Paper.«thm:complete-calm»`); inline claims are named
`«<enclosing label>/<slug>»`.  Each declaration states the result explicitly,
quotes the paper in its docstring, and is proved by a one-line reference to
the library.
-/
