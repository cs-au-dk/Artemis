type zchaff_solver
type zcore_database
type clause = int array
external zchaff_InitManager : unit -> zchaff_solver = "zchaff_InitManager"
external zchaff_ReleaseManager : zchaff_solver -> unit
  = "zchaff_ReleaseManager"
external zchaff_SetNumVariables : zchaff_solver -> int -> unit
  = "zchaff_SetNumVariables"
external zchaff_AddVariable : zchaff_solver -> int = "zchaff_AddVariable"
external zchaff_AddClause : zchaff_solver -> clause -> int -> unit
  = "zchaff_AddClause"
external zchaff_DeleteClauseGroup : zchaff_solver -> int -> unit
  = "zchaff_DeleteClauseGroup"
external zchaff_Reset : zchaff_solver -> unit = "zchaff_Reset"
external zchaff_AllocClauseGroupID : zchaff_solver -> int
  = "zchaff_AllocClauseGroupID"
external zchaff_SetTimeLimit : zchaff_solver -> float -> unit
  = "zchaff_SetTimeLimit"
external zchaff_GetVarAsgnment : zchaff_solver -> int -> int
  = "zchaff_GetVarAsgnment"
external zchaff_Solve : zchaff_solver -> int = "zchaff_Solve"
external zchaff_NumLiteral : zchaff_solver -> int = "zchaff_NumLiterals"
external zchaff_NumClauses : zchaff_solver -> int = "zchaff_NumClauses"
external zchaff_NumVariables : zchaff_solver -> int = "zchaff_NumVariables"
