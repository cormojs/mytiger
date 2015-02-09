signature TEMP = 
sig
  eqtype temp
  val newtemp : unit -> temp
  structure Table : TABLE sharing type Table.key = temp
  val makestring : temp -> string

  type label = Symbol.symbol
  val newlabel : unit -> label
  val namedLabel : string -> label
end

structure Temp : TEMP = 
struct
  type temp = int
  val temporary = ref 0
  fun newtemp () =
      (temporary := !temporary + 1;
       !temporary)

  fun makestring i = "t" ^ Int.toString i

  structure Table = IntMapTable(type key = temp
			        fun getInt i = i)
			       
  type label = Symbol.symbol
  local val labelNum = ref 0
  in fun newlabel () = 
	 let val lnum = (labelNum := !labelNum + 1;
			 !labelNum)
	 in Symbol.symbol("L" ^ Int.toString lnum)
	 end
  end
  val namedLabel = Symbol.symbol
end
