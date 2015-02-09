structure AST = 
struct

type pos = int


datatype lvalue =
	 IDLValue of string
       | FieldLValue of lvalue * string
       | ArrayLValue of lvalue * exp

and exp =
      NilExp
    | LValueExp of lvalue
    | IntExp of int
    | StringExp of string
    | LetExp of { pos: pos }


datatype decs =
	 FunDec
       | VarDec
       | TypDec

end
