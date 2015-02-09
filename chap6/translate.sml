signature TRANSLATE = 
sig
  type level
  type access

  val outermost : level
  val newLevel : { parent: level, name: Temp.label, 
                   formals: bool list } -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access
end

structure Translate : TRANSLATE = 
struct
  struct Frame = MIPSFrame

  datatype level = 
           Top
         | Level of { frame : Frame.frame, parent : level }
  val access = level * Frame.access
  val outermost = Global
  fun formals (Top) = []
    | formals ( = 
end
