-- This module serves as the root of the `LeanCordix` library.
-- Import modules here that should be built as part of the library.
--
-- The canonical full-context model is split into `Basic`, `Step`, `Approx`,
-- `Recovery`, and `Trace`.  It depends on the shared bottom layers
-- (`Revertible`, `Coeffect`, `Context`, `FullCtx`, `Iterator`, and the
-- standalone `StepKind`/iterator-independence infrastructure).
import LeanCordix.Basic
import LeanCordix.Revertible
import LeanCordix.Coeffect
import LeanCordix.Context
import LeanCordix.FullCtx
import LeanCordix.Iterator
import LeanCordix.Step
import LeanCordix.Approx
import LeanCordix.Recovery
import LeanCordix.Trace
import LeanCordix.WellFormed
import LeanCordix.Progress
import LeanCordix.Termination
import LeanCordix.Vestigial
import LeanCordix.Invariance
import LeanCordix.Equivariance
import LeanCordix.Coherence
import LeanCordix.TableConfined

import LeanCordix.Confluence
