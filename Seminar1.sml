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
	    | ListP lp => (case exp of List l => if not ((List.length lp) = (List.length l))
						 then NONE
						 else if (List.foldl (fn(x,y)=>y andalso isSome (match x)) true (ListPair.zip(l,lp)))
						 then SOME(List.foldl (fn(x,y)=>y@(valOf (match x))) [] (ListPair.zip(l,lp)))
						 else NONE
				     | _ => NONE)
	    | UnorderedListP ulp => NONE
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
      Operator("/",Pair([ Operator("-",Pair([Operator("*",Pair([derivative a var,b])),Operator("*",Pair([a,derivative b var]))])),Operator("*",Pair([b,b]))]))
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
	if not (null(List.filter (fn(x)=>(x)=Constant(0)) list))
	then [Constant(0)]
	else if null(List.filter (fn(x)=>not((x)=Constant(1))) list)
	then [Constant(1)]
	else List.filter (fn(x)=>not((x)=Constant(1))) list
							  
      fun checkSum list =
	List.filter (fn(x)=>not((x)=Constant(0))) list

      fun checkDivision exp1 exp2 =
	if (exp1 = Constant(0))
	then Constant(0)
	else case exp2 of Constant(1)=> exp1
			| _ => Operator("/", Pair([exp1, exp2])) 
  in
      case exp of Operator("+", Pair p) =>
		  checkEmpty (Operator("+", Pair(checkSum (List.map (fn(x)=>removeEmpty (checkEmpty x)) p))))
		| Operator("+", List l) =>
		  checkEmpty (Operator("+", List(checkSum (List.map (fn(x)=>removeEmpty (checkEmpty x)) l))))
		| Operator("-", Pair p) =>
		  checkEmpty (Operator("-", Pair(checkSum (List.map (fn(x)=>removeEmpty (checkEmpty x)) p))))
		| Operator("-", List l) =>
		  checkEmpty (Operator("-", List(checkSum (List.map (fn(x)=>removeEmpty (checkEmpty x)) l))))	      
		| Operator("*", Pair p) =>
		  checkEmpty (Operator("*", Pair(checkProduct (List.map (fn(x)=>removeEmpty (checkEmpty x)) p))))
		| Operator("*", List l) =>
		  checkEmpty (Operator("*", List(checkProduct (List.map (fn(x)=>removeEmpty (checkEmpty x)) l))))
		| Operator("/", Pair(a::b::nil)) =>
		  checkEmpty (Operator("/", Pair([checkDivision (removeEmpty (checkEmpty a)) (removeEmpty (checkEmpty b))])))
		| _ => exp
  end

fun combinations sez =
  let
      fun explode (x::nil) =
	List.map (fn(y)=>[y]) x
      
      fun append a b =
	List.foldl (fn(x,y)=>y@x) [] (List.map (fn(b1)=>(List.map (fn(a1)=> b1@[a1]) a)) b)
      
      fun aux acc sez =
	case sez of [] => acc
		  | g::r => aux (append g acc) r	
  in
      case sez of [] => []
		| g::r => aux (explode [g]) r
  end

fun flatten exp =
  let
      fun multiply sez =
	List.map (fn(x)=> List.foldl (fn(x,y)=>x@y) [] x) (combinations sez)

      fun flatten_lists exp =
	case exp of Constant c => [[Constant c]]
		  | Variable v => [[Variable v]]
		  | Operator("*", Pair p) => multiply (List.map (fn(x)=> flatten_lists x) p)
		  | Operator("*", List l) => multiply (List.map (fn(x)=> flatten_lists x) l)
		  | Operator("+", Pair p) => List.foldl (fn(x,y)=>y@(flatten_lists x)) [] p
		  | Operator("+", List l) => List.foldl (fn(x,y)=>y@(flatten_lists x)) [] l			 
		  | _ => [[exp]]
  in
      Operator("+", List(List.map (fn(x)=>Operator("*", List(x))) (flatten_lists exp)))
  end


fun joinSimilar (Operator("+", list)) =
  let
      fun equalSets set1 set2 =
	let
	    fun exists x set =
	      not (null (List.filter (fn(y)=> y = x) set))
	    fun removeFirst acc x set =
	      case set of g::r => if(g = x) then acc@r else removeFirst (acc@[g]) x r
			| _ => set
	in
	    case set1 of g::r => if(exists g set2) then (equalSets r (removeFirst [] g set2)) else false
		       | [] => (null set2)
	end
      fun getVars izr = case izr of Variable v => [v]
				  | Operator("*", Pair p) => List.foldl (fn(x,y)=>y@(getVars x)) [] p
				  | Operator("*", List l) => List.foldl (fn(x,y)=>y@(getVars x)) [] l
				  | _ => []

      fun getConsts izr = case izr of Constant c => c
				  | Operator("*", Pair p) => List.foldl (fn(x,y)=>y + (getConsts x)) 0 p
				  | Operator("*", List l) => List.foldl (fn(x,y)=>y + (getConsts x)) 0 l
				  | _ => 0
	
      fun standardize exp =
	case exp of Constant c => [Constant 1, Constant c]
		  | Variable v => [Constant 1, Variable v]
		  | Operator("*", Pair p) => (p @ [Constant 1])
		  | Operator("*", List l) => (l @ [Constant 1])
		  | _ => [exp]

      fun getConst (Constant c) = c
			     
      fun multiplyConsts a =
	[Constant(List.foldl (fn(x,y)=>case x of Constant c => y*c | _ => y) 1 a)] @
	List.filter (fn(x)=>case x of Constant c => false | _ => true) a

      fun sumConsts a =
	[Constant (List.foldl (fn(x,y)=>y+getConst(hd x)) 0 a )] @ (tl(hd a))
	
		    
      fun eq_classes f sez =
	case sez of [] => []
		  | g::r =>
		    let
			fun get_eq_list seznam =
			  [[g] @ List.filter (fn(x)=>f x (g)) (r)]
		    in
			get_eq_list sez @
			eq_classes f (List.filter (fn(x)=>f x (g) = false) (r))
		    end

      fun compareFun set1 set2 =
	equalSets (List.map (fn(x)=>getVars x) set1) (List.map (fn(x)=>getVars x) set2)

      val listedSimilar = case list of List l=>eq_classes (compareFun) (List.map (fn(x)=>multiplyConsts x) (List.map (fn(x)=>standardize x) l))
		 | _ => raise InvalidExpression (Operator("+", list)) 
  in
      Operator("+", List (List.map (fn(x)=>Operator("*", List x)) (List.map (fn(x)=>sumConsts x) listedSimilar)))
  end

fun divide (e1,e2) =
  let
      fun standardize (Operator("+", List l)) =
	List.map (fn(x)=> case x of Operator("*", List s) => s | _ => [x]) l

      fun getConst sez = case hd sez of Constant c => c | _ => 0

      fun countVars sez = List.foldl (fn(x,y)=>y+(case x of Variable v => 1 | _ => 0)) 0 sez

      fun parse pol =
	List.map (fn(x)=> (getConst x, countVars x) ) pol

      fun sort (pol:(int*int) list) =
	case pol of [] => []
	    | [x] => [x]
	    | g :: r =>
	      let
		  fun partition seznam =
		    sort(List.filter (fn(x)=>(#2 x)>(#2 g)) seznam) @ [g] @
		    sort(List.filter (fn(x)=>(#2 x)<=(#2 g)) seznam)
	      in
		  partition r
	      end 
      
      val e1ParsedSorted = sort (parse (standardize (joinSimilar (flatten e1))))
      val e2ParsedSorted = sort (parse (standardize (joinSimilar (flatten e2))))

      fun divide (p1:(int*int)list) (p2:(int*int)list) =
	((#1 (hd p1)) div (#1 (hd p2)), (#2 (hd p1))-(#2 (hd p2)))

      fun multiply (a,b) (pol:(int*int)list) =
	List.map (fn(x)=> (~(#1 x)*a, (#2 x)+b)) pol

      fun subtract (p1:(int*int)list) (p2:(int*int)list) =
	case p2 of [] => p1
		 | g::r => subtract
			       (if not (null (List.filter (fn(x)=>(#2 x)=(#2 g)) p1))
				then (List.map (fn(x)=>if((#2 g)=(#2 x)) then ((#1 x)+(#1 g), #2 g) else x) p1)
				else (sort (p1@[g]))) r

      fun removeZeros (pol:(int*int)list) = List.filter (fn(x)=> not ((#1 x)=0)) pol

      fun getVars x =
	if x = 0
	then []
	else [Variable("x")] @ getVars (x-1)
							
      fun division pol1 pol2 =
	    if pol1 = []
	    then []
	    else [divide pol1 pol2] @ division (removeZeros (subtract (pol1) (multiply (divide pol1 pol2) pol2))) (pol2)
  in
      removeEmpty (Operator("+", List (List.map (fn(x)=>Operator("*", List([Constant(#1 x)]@(getVars (#2 x))))) (division e1ParsedSorted e2ParsedSorted))))
  end


    
(*(*--------------testi------------------------------------------------------------------*)

(* 1 + (((x+3)*(3+x) + x + (3*x)) *)
val test_case_flatten = (Operator ("+", List [
				       Constant 1,
				       Operator ("+", List [
						     Operator ("*", Pair [
								   Operator ("+", Pair [Variable "x", Constant 3]),
								   Operator ("+", Pair [Constant 3, Variable "x"])]),
						     Variable "x",
						     Operator ("*", Pair [Constant 3, Variable "x"])])]))

val test_case_combinations = [[1,3],[4],[2,5,1]]

(* 3*x + x*x *)
val test_case_derivative = (Operator ("+", Pair [
					  Operator ("*", Pair [
							Constant 3,
							Variable "x"]),
					  Operator ("*", Pair [
							Variable "x",
							Variable "x"])]))
(*1 + 3*1 + 5*x + x + x*3 + x*x*)		       
val test_case_joinSimilar = (Operator ("+", List [
					   Constant 1,
					   Operator ("*", Pair [Constant 3, Constant 1]),
					   Operator ("*", Pair [Constant 5, Variable "x"]),
					   Variable "x",
					   Variable "y",
					   Operator ("*", List [Variable "x", Constant 3]),
					   Operator ("*", List [Variable "x", Variable "x"])]))

val test_case_match = (Operator("+", Pair [
				    Operator ("*", List [Variable "a", Variable "a"]),
				    Operator ("*", List [Variable "b", Variable "b"])]),
		       OperatorP("+", PairP [VariableP "A", VariableP "B"]))

val test_case_divide = (Operator ("+", List [
    Operator ("*",List [Constant 12,Variable "x",Variable "x",Variable "x",Variable "x",Variable "x"]),
    Operator ("*",List [Constant 18,Variable "x",Variable "x",Variable "x"]),
    Operator ("*",List [Constant 3, Operator("*", Pair[Variable "x",Variable "x"])]),
    Operator ("*",Pair [Constant 6,Variable "x"]),
    Operator("+", List [Constant 1, Constant 2])
]), Operator ("+", List [
    Operator ("*",List [Constant 3]),
    Operator ("*",List [Constant 3,Variable "x",Variable "x"])
]))

val test_derivative = removeEmpty (derivative test_case_derivative "x");
			  
val test_combinations = combinations test_case_combinations
			  
val test_flatten = flatten test_case_flatten

val test_joinSimilar = joinSimilar test_case_joinSimilar

val test_divide = divide test_case_divide;

*)
