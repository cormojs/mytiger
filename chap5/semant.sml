signature SEMANT = sig
  val transProg : Absyn.exp -> unit
end

structure Semant :> SEMANT = struct
  structure A = Absyn
  structure Ty = Types
  type expty = { exp: unit, ty : Env.ty }
  val err = ErrorMsg.error
  exception ErrMsg

  val nested = ref false

  fun checkInt({exp, ty}, pos) = 
      case ty of
	  Ty.INT => ()
	| _  => err pos ("int required: " ^ Ty.toString ty)

  fun checkUnit({exp, ty}, pos) =
      case ty of
  	  Ty.UNIT => ()
  	| _  => err pos "unit required"

  fun checkArgs([], [], pos) = ()
    | checkArgs(a::args, f::formals, pos) = 
      if a = f
      then checkArgs(args, formals, pos)
      else err pos ("function args don't match\n"
		    ^ "arg: " ^ Ty.toString a
		    ^ ", formal: " ^ Ty.toString f
		   )
    | checkArgs(_, _, pos) = err pos "function args don't match"

  fun checkEq({exp = e1, ty = ty1},
  	      {exp = e2, ty = ty2}, pos) = 
      if ty1 = ty2 
      then ()
      else err pos "same type required"

  fun nameType(Ty.NAME(sym, ty), pos) =
      (case !ty of 
	   NONE => (err pos ("incomplete type name: " ^ Symbol.name sym) ;
		    raise ErrMsg)
	|  SOME(t) => nameType(t, pos))
    | nameType(Ty.ARRAY(ty,r), pos) = Ty.ARRAY(nameType(ty, pos), r)
    | nameType (t, pos) = t

  fun transTy(tenv, ty) = 
      case ty of
	  A.NameTy(name, pos) => 
	  (case Symbol.look(tenv, name) of
	       NONE => (err pos "undefined type";
			Ty.UNIT)
	     | SOME(typ) => typ)
	| A.RecordTy(fields) => 
	  let fun fieldType ({ name, escape, typ, pos }) = 
		  case Symbol.look(tenv, typ) of
		      SOME(t) => (name, t)
		    | NONE => (err pos "undefined type";
			       (name, Ty.UNIT))
	      fun checkDup ([]) = ()
		| checkDup ((name, pos)::names) = 
		  let fun chk ((x, _), []) = ()
			| chk ((x, pos), (y, pos')::rest) = 
			  if x = y 
			  then err pos "duplicate name in a record"
			  else chk((y, pos'), rest)
		  in chk((name, pos), names)
		  end
	  in (checkDup(ListPair.zip(map #name fields, map #pos fields));
	      Ty.RECORD(map fieldType fields, ref ()))
	  end
	  | A.ArrayTy(name, pos) =>
	    case Symbol.look(tenv, name) of
		NONE => (err pos "undefined type";
			 Ty.ARRAY(Ty.UNIT, ref ()))
	      | SOME(ty) => (Ty.ARRAY(ty, ref()))

  fun transExp(venv, tenv) = 
      let fun trexp (A.OpExp{ left, oper, right, pos}) = 
	      (checkInt(trexp left, pos);
	       checkInt(trexp right, pos);
	       {exp = (), ty = Ty.INT })
	    | trexp (A.NilExp) = 
	      { exp = (), ty = Ty.NIL }
	    | trexp (A.VarExp var) = trvar var
	    | trexp (A.IntExp i) = 
	      { exp = (), ty = Ty.INT }
	    | trexp (A.StringExp s) = 
	      { exp = (), ty = Ty.STRING }
	    | trexp (A.CallExp {func, args, pos}) = 
	      (case Symbol.look (venv, func) of
		   SOME(Env.FunEntry { formals, result}) => 
		   let val argsTyp = map (#ty o trexp) args
		   in (checkArgs(argsTyp, formals, pos);
		       { exp = (), ty = result }) end
		 | _ => ((err pos "called function doesn't exist");
			 { exp = (), ty = Ty.UNIT }))
	    | trexp (A.SeqExp [(e, pos)])   = trexp e
	    | trexp (A.SeqExp ((e, pos)::es)) = trexp (A.SeqExp es)
	    | trexp (A.SeqExp [])    = { exp = (), ty = Ty.UNIT }
	    | trexp (A.AssignExp { var, exp, pos }) = 
	      let val { exp = _, ty = leftTyp }  = trvar var
		  val { exp = _, ty = rightTyp } = trexp exp
	      in if nameType(leftTyp, pos) = rightTyp 
		 then { exp = (), ty = rightTyp }
		 else (err pos "left type and right type don't match";
		       { exp = (), ty = rightTyp })
	      end
	    | trexp (A.IfExp { test, then', else', pos }) =
	      (checkInt(trexp test, pos);
	       case else' of
	    	   SOME(elseExp) =>
	    	   let val { exp = _, ty = result } = trexp elseExp
	    	   in (checkEq(trexp then', trexp elseExp, pos);
	    	       { exp = (), ty = result })
	    	   end
	    	 | NONE => (checkUnit(trexp then', pos);
	    		    { exp = (), ty = Types.UNIT }))
	    | trexp (A.WhileExp { test, body, pos }) = 
	      (checkInt(trexp test, pos);
	       nested := true;
	       checkUnit(trexp body, pos);
	       nested := false;
	       { exp = (), ty = Ty.UNIT })
	    | trexp (A.ArrayExp { typ, size, init, pos }) = 
	      let val { exp = _, ty = typ' } = trexp init
		  fun getArrRef(name) = 
		      case Symbol.look(tenv, name) of
			SOME(ty) => 
			(case nameType(ty, pos) of
			     Ty.ARRAY(_, rf) => rf
			   | _ => (err pos "not an array type"; 
				   ref ()))
			| NONE => (err pos ("undefined array type: " 
					    ^ Symbol.name name);
				   ref ())
		  val arrRef = getArrRef(typ)
	      in { exp = (), ty = Ty.ARRAY(typ', arrRef) } end 
	    | trexp (A.LetExp { decs, body, pos}) = 
	      let fun trdec(dec, {tenv, venv}) = transDec(venv, tenv, dec)
		  val { venv = venv', tenv = tenv' } = 
		      foldl trdec { tenv = tenv, venv = venv } decs
	      in transExp(venv', tenv') body
	      end
	    | trexp (A.RecordExp {fields, typ, pos} ) = 
	      let val (tyFields, tyRef) = 
		      case Symbol.look(tenv, typ) of
			  SOME(ty) => 
			  (case nameType(ty, pos) of
			       Ty.RECORD(tyFields, tyRef) => (tyFields, tyRef)
			    |  _ => (err pos "not a record type: ";
				      ([], ref ())))
			| NONE =>    (err pos "undefined type";
				      ([], ref ()))
		  fun checkRecords ([], [], _) = ()
		    | checkRecords ((name, exp, pos)::fields, tyFields, pos') = 
		      (case (List.partition (fn (name', _) => name' = name)
					    tyFields) of
			   ([(_, ty)], rest) => 
			   let val { exp = _, ty = ty' } = trexp exp
			   in if (ty = ty' orelse ty' = Ty.NIL)
			      then checkRecords(fields, rest, pos')
			      else (err pos "doesn't match field type")
			   end
			 | (_, _) => (err pos "cannot find field name"))
		    | checkRecords (_, _, pos) = 
		      err pos "doesn't match number of field"
	      in (checkRecords(fields, tyFields, pos);
		  { exp = (), ty = Ty.RECORD(tyFields, tyRef) }) 
	      end
	    | trexp (A.ForExp { var, escape, lo, hi, body, pos }) = 
	      let val venv' = Symbol.enter(venv, var, 
					   Env.VarEntry { ty = Ty.INT })
	      in 
		  (checkInt(trexp lo, pos);
		   checkInt(trexp hi, pos);
		   nested := true;
		   checkUnit(transExp (venv', tenv) body, pos);
		   nested := false;
		   { exp = (), ty = Ty.UNIT})
	      end
	    | trexp (A.BreakExp(pos)) = 
	      if !nested 
	      then { exp = (), ty = Ty.UNIT}
	      else (err pos "break is not in while or for stmt";
		    { exp = (), ty = Ty.UNIT})
	  and trvar (A.SimpleVar (sym, pos)) =
	      (case Symbol.look(venv, sym) of
	  	   SOME(Env.VarEntry{ty}) => { exp = () , ty = nameType(ty, pos) }
	  	 | _ => (err pos "undefined variable";
			 { exp = (), ty = Ty.UNIT }))
	    | trvar (A.FieldVar (var, sym, pos)) = 
	      let val { exp = _, ty = recordTyp } = trvar var
		  fun lookupFields(sym, (sym', typ)::rest) = 
		      if sym = sym'
		      then { exp = (), ty = typ }
		      else lookupFields(sym, rest)
		    | lookupFields(_, []) = 
		      (err pos "couldn't find such field";
		       { exp = (), ty = Ty.UNIT })
	      in (case nameType(recordTyp, pos) of 
		      Ty.RECORD(fields, _) => lookupFields(sym, fields)
		    | _ => (err pos "record required";
			    { exp = (), ty = Ty.UNIT }))
	      end
	    | trvar (A.SubscriptVar (var, exp, pos)) = 
	      let val { exp = _, ty = varTyp } = trvar var
	      in (case nameType(varTyp, pos) of
		      Ty.ARRAY(arTyp, _) =>
		      (checkInt(trexp exp, pos);
		       { exp = (), ty = arTyp })
		    | _ => (err pos "array required";
			    { exp = (), ty = Ty.UNIT }))
	      end
      in trexp end
  and transDec (venv, tenv, A.VarDec { name, typ = typOpt, init, pos, ...}) =
      let val { exp = _, ty = initTyp } = transExp (venv, tenv) init
      in (case typOpt of 
	      SOME(sym, pos1) => 
	      (case Symbol.look(tenv, sym) of
		   SOME(typ') => 
		   let val typ'' = nameType(typ', pos1)
		   in if typ'' = initTyp
		      then { tenv = tenv, 
			     venv = Symbol.enter(venv, name,
						 Env.VarEntry { ty = typ'' }) }
		      else (err pos ("don't match\n"
				     ^ "right: " ^ Ty.toString(typ'')
				     ^ "\nleft : " ^ Ty.toString(initTyp) 
				     ^ "\n");
			 { tenv = tenv, venv = venv })
		   end
		 | NONE => (err pos "couldn't find such type";
			    { tenv = tenv, venv = venv }))
	    | NONE => ({ tenv = tenv, 
			 venv = Symbol.enter(venv, name,
					     Env.VarEntry { ty = initTyp }) }))
      end
    | transDec (venv, tenv, A.TypeDec(decs)) =
      let val names = map #name decs
    	  fun addType(name, tbl) =
    	      Symbol.enter(tbl, name, Types.NAME(name, ref(NONE)))
    	  val tenv' = foldl addType tenv names
	  val nameTypes = map (fn {name, ty, pos} => 
				  (name, transTy(tenv', ty))) decs
	  fun updateType (name, typ) = 
	      let val SOME(Types.NAME(_, tyRef)) = Symbol.look(tenv', name)
	      in (tyRef := SOME(nameType(typ, 0));
		  err 0 ("updated " ^ Symbol.name name 
			  ^" = " ^ Ty.toString typ)) end
      in (app updateType nameTypes;
	  { tenv = tenv', venv = venv }) end
    | transDec (venv, tenv, A.FunctionDec(fundecs)) = 
      let fun getFieldType { name, escape, typ, pos } = 
	      case Symbol.look(tenv, typ) of
		  SOME(ty) => ty
		| NONE => (err pos "undefined param type";
			   Ty.UNIT)
	  fun entryFunDec({ name, params, result, body, pos},
			  { tenv, venv }) =
	      let val paramTypes = map getFieldType params
		  val resultType = 
		      case result of 
			  SOME(name, pos) => 
			  (case Symbol.look(tenv, name) of
			       SOME(ty) => ty 
			     | NONE => (err pos "undefined return type";
					Ty.UNIT))
			| NONE => Ty.UNIT
	      in { tenv = tenv, 
		   venv = Symbol.enter(venv, name, 
				       Env.FunEntry { formals = paramTypes,
						      result = resultType }) }
	      end 
	  fun checkBodyType(tenv, venv,
			    { name, params, result, body, pos }) = 
	      let val resultType = 
		      case result of
			  SOME(name, pos) => 
			  (case Symbol.look(tenv, name) of
			       SOME(ty) => ty 
			     | NONE => (err pos "undefined return type";
					Ty.UNIT))
			| NONE => Ty.UNIT
		  fun enterParam(param, venv) = 
		      let val { name, escape, typ, pos } = param
		      in Symbol.enter(venv, name, 
				      Env.VarEntry { ty = getFieldType param})
		      end 
		  val venv' = foldl enterParam venv params
		  val { exp = _, ty = bodyType } = transExp (venv', tenv) body
	      in (if bodyType <> resultType 
		  then (err pos "body type doesn't match result type")
		  else ()) end
	  val { tenv = tenv', venv = venv' } =  
	      foldl entryFunDec { tenv = tenv, venv = venv } fundecs

      in (app (fn func => checkBodyType(tenv', venv', func)) fundecs;
	  { tenv = tenv', venv = venv' })
      end

  fun transProg(exp) = (transExp (Env.base_venv, Env.base_tenv) exp;())
end
