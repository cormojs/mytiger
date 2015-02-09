structure Test = struct
  fun test(filename) = 
      let val absyn = Parse.parse(filename)
      in (
	  PrintAbsyn.print(TextIO.stdOut, absyn);
	  Semant.transProg(absyn)
      ) end
end
