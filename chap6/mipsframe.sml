structure MIPSFrame : FRAME = 
struct 
  datatype access = 
           InReg of Temp.temp
         | InFrame of int
  type frame = { name : Temp.label, 
                 formals : 
