(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 * Copyright (c) - 2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val process_declassify : oside -> backward
val process_undeclassify : oside -> backward
val process_secrnd : oside -> backward
val process_secrndasgn : backward
