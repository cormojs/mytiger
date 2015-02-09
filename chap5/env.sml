signature ENV = sig
  type access
  type ty
  datatype enventry = VarEntry of { ty: ty }
	            | FunEntry of { formals: ty list, 
				    result: ty }
  val base_tenv : ty Symbol.table
  val base_venv : enventry Symbol.table
end

structure Env : ENV = struct
  type access = unit ref
  type ty = Types.ty
  fun enter ((symbol, entry), env) = Symbol.enter(env, symbol, entry)
  datatype enventry = VarEntry of { ty: ty }
	            | FunEntry of { formals: ty list, result: ty }
  val base_tenv = foldr enter Symbol.empty [
	  (Symbol.symbol("int"), Types.INT),
	  (Symbol.symbol("string"), Types.STRING)
      ]
  val base_venv = Symbol.empty
end
