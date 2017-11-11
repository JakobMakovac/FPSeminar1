Control.Print.printDepth := 100;

datatype expression =  Constant of int |
		       Variable of string |
		       Operator of string * expression |
		       Pair of expression list |
		       List of expression list

datatype pattern = ConstantP of int
		 | VariableP of string
		 | OperatorP of string * pattern
		 | PairP of pattern list
		 | ListP of pattern list
		 | UnorderedListP of pattern list
		 | Wildcard

exception InvalidVariable of string
exception InvalidExpression of expression

fun cross (sez1, sez2) =
  List.foldl (fn(x,y)=> y@x) [] (List.map (fn(x)=>List.map (fn(y)=> (x,y)) sez2) sez1)

fun match (exp, pat) =
  case pat of ConstantP cp => (case exp of Constant c => if cp=c then SOME([]) else NONE
					 | _ => NONE)
	    | VariableP vp => (SOME([(vp, exp)]))
	    | OperatorP(ap, bp) => (case exp of Operator(a,b) => if ap=a then match(b, bp) else NONE
					      | _ => NONE )
	    | PairP [ap, bp] => (case exp of Pair [a, b] => if(isSome (match(a,ap)) andalso isSome (match(b,bp)))
							    then SOME((valOf (match(a,ap)))@(valOf (match(b,bp))))
							    else NONE
					   | _ => NONE)
	    | ListP lp => (case exp of List l => if (List.foldl (fn(x,y)=>y andalso isSome (match x)) true (ListPair.zip(l,lp)))
						 then SOME(List.foldl (fn(x,y)=>y@(valOf (match x))) [] (ListPair.zip(l,lp)))
						 else NONE
				     | _ => NONE)
	    | Wildcard => SOME([])
	    | _ => NONE 
		       
fun eval (var: (string*int) list) exp =
  case exp of

(*----------Pattern matching za vračanje celoštevilskih vrednosti---------------------------------------------*)
      
      Constant c => c
    (*Filter pregleda seznam spremenljivk in vrne prvo vezavo, sicer proži izjemo*)
    | Variable v => (case (List.filter (fn(x)=> v = (#1 x)) var) of [] => raise InvalidVariable(v)
								  | g::r => (#2 g))
(*----------Pattern matching za vse podprte operacije---------------------------------------------------------*)
				
    (*Pair(a::b::nil) zagotavlja da ima Pair samo dva elementa*)
    | Operator("-", Pair(a::b::nil)) => (eval var a) - (eval var b)
    (*Pri deljenju preverjamo veljavnost(deljenje z 0)*)
    | Operator("/", Pair(a::b::nil)) => if((eval var b)=0)
					then raise InvalidExpression(exp)
					else (eval var a) div (eval var b)			     
    | Operator("%", Pair(a::b::nil)) => if((eval var b)=0)
					then raise InvalidExpression(exp)
					else (eval var a) mod (eval var b)				     
    | Operator("+", Pair(a::b::nil)) => (eval var a) + (eval var b)
    | Operator("*", Pair(a::b::nil)) => (eval var a) * (eval var b)
    | Operator("+", List sez) => List.foldl (fn(x,y)=> y + (eval var x)) 0 sez
    | Operator("*", List sez) => List.foldl (fn(x,y)=> y * (eval var x)) 1 sez
    | _ => raise InvalidExpression exp
  
fun derivative exp var =
  case exp of

(*---------Pattern matching za odvajanje konstant in spremenljivk--------------------------------------------*)
      
      Constant c => Constant(0)
    | Variable v => Constant(if(v=var)then 1 else 0)

(*---------Pattern matching za pravila odvajanja izrazov-----------------------------------------------------*)

    (* (f+g)' = f' + g' *)
    | Operator("+",Pair(a::b::nil)) => Operator("+", Pair([derivative a var, derivative b var]))
    (* (f-g)' = f' - g' *)
    | Operator("-",Pair(a::b::nil)) => Operator("-", Pair([derivative a var, derivative b var]))
    (* (f*g)' = f'*g + f*g' *)
    | Operator("*", Pair(a::b::nil)) =>
      Operator("+",Pair([Operator("*",Pair([derivative a var, b])),Operator("*",Pair([a, derivative b var]))]))
    (* (f/g)' = (f'*g - f*g')/g^2 *)
    | Operator("/",Pair(a::b::nil)) =>
      Operator("/",Pair([ Operator("-",Pair([Operator("*",Pair([derivative a var,b])),Operator("*",Pair([a,derivative b var]))])),Operator("*",Pair([a,b]))]))
    | _ => raise InvalidExpression exp

fun removeEmpty exp =
  let
      fun checkEmpty exp =
	case exp of Operator(_, Pair(a::nil)) => a
		  | Operator(_, List(a::nil)) => a
		  | Operator(_, Pair(nil)) => Constant(0)
		  | Operator(_, List(nil)) => Constant(0)
		  | _ => exp
			     
      fun checkProduct list =
	case List.filter (fn(x)=>(x)=Constant(0)) list of g::r => [Constant(0)]
							| [] => List.filter (fn(x)=>not((x)=Constant(1))) list
      fun checkSum list =
	List.filter (fn(x)=>not((x)=Constant(0))) list

      fun checkDivision exp1 exp2 =
	case exp2 of Constant(1)=> exp1
			       | _ => Operator("/", Pair([exp1, exp2])) 
  in
      case exp of Operator("+", Pair p) =>
		  checkEmpty (Operator("+", Pair(checkSum (List.map (fn(x)=>removeEmpty x) p))))
		| Operator("+", List l) =>
		  checkEmpty (Operator("+", List(checkSum (List.map (fn(x)=>removeEmpty x) l))))
		| Operator("-", Pair p) =>
		  checkEmpty (Operator("+", Pair(checkSum (List.map (fn(x)=>removeEmpty x) p))))
		| Operator("-", List l) =>
		  checkEmpty (Operator("+", List(checkSum (List.map (fn(x)=>removeEmpty x) l))))	      
		| Operator("*", Pair p) =>
		  checkEmpty (Operator("*", Pair(checkProduct (List.map (fn(x)=>removeEmpty x) p))))
		| Operator("*", List l) =>
		  checkEmpty (Operator("*", List(checkProduct (List.map (fn(x)=>removeEmpty x) l))))
		| Operator("/", Pair(a::b::nil)) =>
		  checkEmpty (Operator("/", Pair([checkDivision (removeEmpty a)(removeEmpty b)])))
		| _ => exp
  end      
	  
fun joinSimilar exp =
  let
      fun equivalence_classes f seznam = 
	case seznam of 
	    [] => []
	  | g::r => 
	    let 
		fun get_eq_list sez = 
		  [[g] @ List.filter (fn(x) => f x (g)) (r)]
	    in
		get_eq_list seznam @ equivalence_classes f (List.filter (fn(x) => f x (g) = false) (r))
	    end
		
      fun countVariables exp =
	case exp of Variable v => 1
		  | Operator(_, e) => countVariables e
		  | Pair p => List.foldl (fn(x,y)=>(countVariables x) + y) 0 p
		  | List l => List.foldl (fn(x,y)=>(countVariables x) + y) 0 l
		  | _ => 0

      fun areSimilar exp1 exp2 =
	countVariables exp1 = countVariables exp2	

  in
      case exp of Operator("+", List l) => equivalence_classes areSimilar l
		| Operator("+", Pair p) => equivalence_classes areSimilar p
		| _ => [[exp]]
  end


(* 3*x + 7 + 4*x*x *)
val test_case_derivative = (Operator ("*", Pair [
					  Variable "x",
					  Operator ("*", Pair [
							Constant 3,
							Variable "x"])]))
(*1 + 3*1 + 5*x + x + x*3 + x*x*)		       
val test_case_joinSimilar = (Operator ("+", List [
					   Constant 1,
					   Operator ("*", Pair [Constant 3, Constant 1]),
					   Operator ("*", Pair [Constant 5, Variable "x"]),
					   Variable "x",
					   Operator ("*", List [Variable "x", Constant 3]),
					   Operator ("*", List [Variable "x", Variable "x"])]))

val test_case_match = (Operator("+", Pair [
				    Operator ("*", List [Variable "a", Variable "a"]),
				    Operator ("*", List [Variable "b", Variable "b"])]),
		       OperatorP("+", PairP [VariableP "A", VariableP "B"]))
