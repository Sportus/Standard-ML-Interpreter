(*Author: Sean Brais 5/5/2016
Honors Contact CSE305

Reads through a well formed SML expression and evaluates functions and creates variable bindings if necessary
Programs runs through interpret, where it determines whether line is a function or a variable assignment.  
Either calls handle function, or compute assignment.
Handle function defines function and adds function definition to function map
Compute assignment adds variable name to variable map and the evaluated right hand side of the expression.
This is evaluated using evaluateIntLine.

evaluateIntLine removes variables, if /else statements, functions, and ~ symbols to make a well formed post fix expression.
This is then evaluated and a value is returned.

evaluateFunction uses this same process but does it in functions
*)


(*Custom Map built for use in variable and function maps*)

fun mapContains(map, k) = 
let
	fun head (map) = List.hd(List.hd(map))
	fun getV (map) = List.last(List.hd(map))
in 
	if(length(map) = 0) then false
	else if(head(map) = k) then true
	else mapContains(List.tl(map), k) 
end

fun mapRemoveValue(map, k, nMap) = 
let
	fun hd(map) = List.hd(List.hd(map))
	fun getV(map) = List.last(List.hd(map))
in	
if length(map) = 0 then nMap
else if hd(map) = k then nMap
else mapRemoveValue(List.tl(map), k, nMap @ [[hd(map), getV(map)]])
end
fun mapAdd(map , k, v) =
if (mapContains(map, k)) then mapRemoveValue(map, k, []) @ [[k, v]]
else map @ [[k, v]]


fun mapGetValue(map, k) = 
let
	fun hd(map) = List.hd(List.hd(map))
	fun getV(map) = List.last(List.hd(map))
in 
	if(length(map) = 0) then "NOTFOUND"
	else if(hd(map) = k) then getV(map)
	else mapGetValue(List.tl(map), k) 
end

fun printMap(map) = 
if(length(map) = 0) then "Done"
else(print("KEY: " ^ List.hd(List.hd(map)) ^ "\nVALUE: " ^ mapGetValue(map, List.hd(List.hd(map))) ^ "\n"); printMap(List.tl(map)))

(*A stack that can be used in the program*)
fun peek (stack) = List.last(stack)
fun pop (stack) = List.take(stack, length(stack) - 1)
fun push (stack, item) = stack@[item]

fun removeLast l = List.take(l, length(l) - 1)	
fun removeEnd(l : char list) =  
if(ord(List.last(l)) = ord(#"\r")) then removeEnd(removeLast(l))
else if(ord(List.last(l)) = ord(#"\n")) then removeEnd(removeLast(l))
else implode(l)
						
(*Determines if a ASCII values is found in a particular string of characters*)						
fun contains(s : string, dec : int) = 
let val l = explode(s)
in
if(length(l) = 0) then false
else if(ord(List.hd(l)) = dec) then true
else contains(implode(List.tl(l)), dec)
end

(*Prints string list to console*)
fun printTokens(l : string list) = 
if(length(l)) = 0 then ""
else(print(List.hd(l) ^ " | "); printTokens(List.tl(l)))

fun printStack(l : string list) = 
if(length(l)) = 0 then 1
else (print((List.hd(l)) ^ " | "); printStack(List.tl(l)))

(*Determines whether a specific char is an operator*)
fun isOperator(c : char) =
if c = #"(" orelse c = #")" then true
else if c = #"+" then true
else if c = #"-" then true
else if c = #"*" then true
else if c = #"/" then true
else if c = #"^" then true
else if c = #"~" then true
else if c = #"," then true
else if c = #"=" then true
else if c = #">"  then true
else if c = #"<"  then true
else false

(*Determines whether a specific string is an operator(This is a duplicate function to isOperator -- hacky way to get around type system)*)
fun isOperatorS(s : string) =
if s = "(" orelse s = ")" then true
else if s = "+" then true
else if s = "-" then true
else if s = "*" then true
else if s = "/" then true
else if s = "^" then true
else if s = "~" then true
else if s = "," then true
else if s = "=" then true
else if(s =">") then true
else if(s ="<") then true
else if(s = "=") then true
else if(s = ">=") then true
else if(s = "<=") then true
else false

(*Determines precedence for arithmetic operations*)
fun getPrecedence(s : string) = 

if s = "^" then 3
else if s = "/" orelse s = "*" then 2
else if s = "+" orelse s = "-" then 1
else if s = "(" then 0
else if s = ")" then ~1
else 404

fun f c = if(c = #" ") then true else false
fun getTokens(c, s) = 
	let 
	fun f c1 = if(c = c1) then true else false
	val tokens = String.tokens(f)
	in 
		tokens(s)
	end
fun listToString(l : string list, s :string) = if(length(l) = 0) then s
else listToString(List.tl(l), s ^ List.hd(l)) 

fun removeSpaces(s : string) = 
let 
val t = getTokens(#" ", s)
in 
listToString(t, "")
end	

(*Tokenizes a spaceless string into tokens seperated by operators*)
fun tokenize(s:string, tokens: string list) = 

let 
	val l = explode(s)
	fun buildUntilOperator(l : char list, s : string) = 
	if(length(l) = 0) then s
	else if(isOperator(List.hd(l))) then s
	else buildUntilOperator(List.tl(l), s ^ Char.toString(List.hd(l)))

	fun removeUntilOperator(l : char list) = 
	if(length(l) = 0) then implode(l)
	else if(isOperator(List.hd(l))) then implode(l)
	else removeUntilOperator(List.tl(l))
in 

if(length(l) = 0) then tokens
else if(isOperator(List.hd(l))) then tokenize(implode(List.tl(l)), tokens@[Char.toString(List.hd(l))])
else tokenize(removeUntilOperator(l), tokens @ [buildUntilOperator(l, "")])
end


(*Takes a well formed tokenized infix expression and translates it into PostFix*)	
fun toPostFix(tokens:string list, opStack : string list, out : string list) = 
	let 
		fun buildUntilMatch(inStack : string list, outStack : string list) = 
		let 
			val last = List.last(inStack)
			in
			if(last = "(") then outStack
			else buildUntilMatch(pop(inStack), push(outStack, last)) 
		end

		fun popUntilMatch(inStack : string list) = 
		let 
			val last = List.last(inStack)
			in
			if(last = "(") then pop(inStack)
			else popUntilMatch(pop(inStack)) 
		end
	in 
	if(length(tokens) = 0) andalso length(opStack) = 0 then out
	else if(length(tokens) = 0) andalso length(opStack) >0 then toPostFix([], pop(opStack), push(out, peek(opStack)))
	else if(getPrecedence(List.hd(tokens)) = 0) then toPostFix(List.tl(tokens), push(opStack, List.hd(tokens)), out)
	else if(getPrecedence(List.hd(tokens)) = ~1) then toPostFix(List.tl(tokens), popUntilMatch(opStack), out @ buildUntilMatch(opStack, []))
	else
		 if(length(opStack) = 0) then toPostFix(List.tl(tokens), push(opStack, List.hd(tokens)), out)
		 else if(getPrecedence(peek(opStack)) = 0) then toPostFix (List.tl(tokens), push(opStack, List.hd(tokens)), out)
		 else if(getPrecedence(List.hd(tokens)) > getPrecedence(peek(opStack))) then toPostFix(List.tl(tokens), push(opStack, List.hd(tokens)), out)
		 else toPostFix(tokens, pop(opStack), push(out, peek(opStack)))
	end

(*Evaluates a postfix expression*)	
fun evaluatePostFix(tokens : string list, numStack : int list) = 
let 
		fun compute(s :string, numStack : int list) =
		let 
			val first  : int = peek(numStack)
			val second : int = peek(pop(numStack))
		in
			if(s = "+") then push(pop(pop(numStack)), (second + first))
			else if(s = "-") then push(pop(pop(numStack)), (second - first))
			else if(s = "/") then push(pop(pop(numStack)), (second div first))
			else if(s = "*") then push(pop(pop(numStack)), (second * first))
			else pop(numStack)
		end
in		

if length(tokens) = 0 then Int.toString(peek(numStack))
else if (not(isOperatorS(List.hd(tokens)))) then evaluatePostFix(List.tl(tokens), 
push(numStack, Option.valOf (Int.fromString(List.hd(tokens))) ))
else evaluatePostFix(List.tl(tokens), compute(List.hd(tokens), numStack))
end

(*Removes (~) negative numbers in a well formed infix expression*)
fun removeNegatives(tokens : string list, newTokens : string list) =
let 
	fun replace() = ["(","0", "-"]
	
	fun buildEqualNegative(tokens : string list, newTokens :string list, parens : int) = 
	if(List.hd(tokens) = "(") then buildEqualNegative(List.tl(tokens), (newTokens @ [List.hd(tokens)]), parens + 1)
	else if(parens = 0) then replace() @ newTokens @ [List.hd(tokens), ")" ]
	else if(List.hd(tokens) = ")") then 
		if(parens = 1) then replace() @ newTokens @ [List.hd(tokens), ")" ] 
		else buildEqualNegative(List.tl(tokens), newTokens @ [List.hd(tokens)], parens -1)
	else buildEqualNegative(List.tl(tokens), newTokens @ [List.hd(tokens)], parens)

	fun removeEqualNegative(tokens : string list, parens : int) = 
	if(List.hd(tokens) = "(") then removeEqualNegative(List.tl(tokens), parens + 1)
	else if(parens = 0) then List.tl(tokens)
	else if(List.hd(tokens) = ")") then 
		if(parens = 1) then List.tl(tokens) 
		else removeEqualNegative(List.tl(tokens), parens -1)
	else removeEqualNegative(List.tl(tokens), parens)
	
in 
if(length(tokens)) = 0 then newTokens
else if(List.hd(tokens) = "~") then removeNegatives(buildEqualNegative(List.tl(tokens), [], 0) @ removeEqualNegative(List.tl(tokens), 0) , newTokens)
else removeNegatives(List.tl(tokens), newTokens @ [List.hd(tokens)]) 
end

datatype LineFunction = ASSIGN | FUNCTION | ERROR
datatype LineType = INT | STRING | BOOLEAN

(*Fills in variables*)
fun fillInVariables(tokens : string list, newTokens : string list, map :string list list) =
if(length(map) = 0) then tokens
else if length(tokens) = 0 then newTokens
else if mapContains(map, List.hd(tokens)) then fillInVariables(List.tl(tokens), newTokens@ [mapGetValue(map, List.hd(tokens))], map) 
else fillInVariables(List.tl(tokens), newTokens @ [List.hd(tokens)], map)

(*Gets the argument map for a specified function*)
fun getArgMap(tokens, paremMap, map) = (
if(length(paremMap) = 0) then map
else if(List.hd(tokens) = ")") then map
else if(List.hd(tokens)) = "(" then getArgMap(List.tl(tokens), paremMap, map)
else if(List.hd(tokens)) = "," then getArgMap(List.tl(tokens), paremMap, map)
else getArgMap(List.tl(tokens), List.tl(paremMap), mapAdd(map, List.hd(paremMap), List.hd(tokens))))

(*If function is found in map, particiular string is function*)
fun isFunction(funMap, name ) = mapContains(funMap, name)

fun removeUntilEndOfFunction(l : string list) = 
if(List.hd(l) = ")") then List.tl(l)
else removeUntilEndOfFunction(List.tl(l))

datatype Comparator = EQUALS | LESSTHAN | GREATERTHAN | GREATERTHANOREQUAL | LESSTHANOREQUAL | WRONG

(*Parsers for comparators*)
fun isComparator(s : string) =
if(s = "<") then true
else if(s =">") then true
else if(s = "=") then true
else if(s = ">=") then true
else if(s = "<=") then true
else false


fun getComparator(s : string) =
if(s = "<") then LESSTHAN
else if(s =">") then GREATERTHAN
else if(s = "=") then EQUALS
else if(s = ">=") then GREATERTHANOREQUAL
else if(s = "<=") then LESSTHANOREQUAL
else WRONG

fun compareValues(first,second, comparator) = 
if(comparator = LESSTHAN) then first < second
else if(comparator = GREATERTHAN) then first > second
else if(comparator = EQUALS) then first = second
else if(comparator = GREATERTHANOREQUAL) then  first>=second
else if(comparator = LESSTHANOREQUAL) then  first<=second
else false

(*First statement in if statement*)
fun firstStatement(tokens : string list) = 
let 
	val ifRemovedTokens = List.drop(tokens, 2)
	fun build(tokens : string list, nTokens : string list) = 
	if(isComparator(List.hd(tokens))) then nTokens
	else build(List.tl(tokens), nTokens @[List.hd(tokens)])
	in
build(ifRemovedTokens, [])
end

fun comparator(tokens : string list) = 
let 
	fun find(tokens : string list) = 
	if(isComparator(List.hd(tokens))) then List.hd(tokens)
	else find(List.tl(tokens))
	in
find(tokens)
end
(*Second statement in if statment*)
fun secondStatment(tokens : string list) = 
let 
	fun findUntilEndBlock(tokens, newTokens, numParens) = 
	if(List.hd(tokens) = "(") then findUntilEndBlock(List.tl(tokens), newTokens @ [List.hd(tokens)], numParens + 1)
	else if(List.hd(tokens) = ")") then 
		if(numParens = 0) then newTokens
		else findUntilEndBlock(List.tl(tokens), newTokens @ [List.hd(tokens)], numParens -1)
	else findUntilEndBlock(List.tl(tokens), newTokens @ [List.hd(tokens)], numParens)

	fun build(tokens : string list, nTokens : string list, foundComparator) = 
	if(foundComparator) then findUntilEndBlock(tokens, [], 0)
	else 
	if(isComparator(List.hd(tokens))) then build(List.tl(tokens), nTokens, true)
	else build(List.tl(tokens), nTokens, false)
	in
	build(tokens, [], false)
end

fun removeGenericStatement(tokens : string list, statement : string) = 
let 
	fun removeUntilStatement(tokens) = 
	if(List.hd(tokens) = statement) then List.tl(List.tl(tokens))
	else removeUntilStatement(List.tl(tokens)) 
	
	val statement = removeUntilStatement(tokens) 
	
	fun build(tokens, newTokens, numParens) = 
	if(List.hd(tokens) = ")" andalso numParens = 0) then newTokens
	else if(List.hd(tokens) = ")") then   build(List.tl(tokens), newTokens @ [List.hd(tokens)], numParens - 1)
	else if(List.hd(tokens) = "(") then   build(List.tl(tokens), newTokens @ [List.hd(tokens)], numParens + 1)
	else build(List.tl(tokens), newTokens @ [List.hd(tokens)], numParens)
	in
	build(statement, [], 0)
end

(*Generates an if statement for the program*)
fun generateStatement(tokens) =  
let
	fun notContainsIf(tokens) = 
	if(length(tokens)) = 0 then true
	else if(List.hd(tokens) = "if") then false
	else notContainsIf(List.tl(tokens))
	fun evaluateStatement(tokens) = (evaluatePostFix(toPostFix(tokens, [], []), []))
in

if(notContainsIf(tokens)) then tokens
else
let 
	val first = firstStatement(tokens)
	val second = secondStatment(tokens)
	val comparator = getComparator(comparator(tokens)) 
in 
	if(compareValues(Option.valOf(Int.fromString(evaluateStatement(first))), Option.valOf(Int.fromString(evaluateStatement(second))), comparator)) then removeGenericStatement(tokens, "then")
	else removeGenericStatement(tokens, "else")
end
end

(*Removes functions from a particular expression.  It fills in the function with the value of it when caluclated*)
fun removeFunctions(tokens, nl, funMap, paremMap) = 
let 
	fun evaluateFunction(line : string, varMap : string list list, funMap, paremMap) = 
	let
		val y = (removeSpaces(line))
		val x = (tokenize(y, []))
		val z = fillInVariables(x, [], varMap)
		val c = removeFunctions(z, [], funMap, paremMap)
		val a = removeNegatives(c, [])
		val i = generateStatement(a)
		val postFix = toPostFix(i, [], [])
	in
	(evaluatePostFix(postFix, []))
end

fun getArguments(tokens : string list, parems, funMap, paremMap) = 
		let
		fun getP(tokens : string list, buildArgument : string, argList, numParens : int) = 
			let 
			val hd = List.hd(tokens)
			in
				if (hd = ")" andalso numParens = 0) then argList @ [buildArgument]
				else if(hd = ")") then getP(List.tl(tokens), buildArgument ^ List.hd(tokens), argList, numParens-1)
				else if(hd = "," andalso numParens = 0) then getP(List.tl(tokens),"", argList@[buildArgument], numParens)
				else if(hd = "(") then getP(List.tl(tokens), buildArgument ^ List.hd(tokens), argList, numParens+1)
				else getP(List.tl(tokens), buildArgument ^ List.hd(tokens), argList, numParens)
				end
		fun buildArgMap(tokens, parems, map, funMap, paremMap) = 
		let 
		in
		if(length(tokens) = 0) then map
		else buildArgMap(List.tl(tokens), List.tl(parems), mapAdd(map, List.hd(parems), evaluateFunction(List.hd(tokens), [], funMap, paremMap)), funMap, paremMap)
		end
	in
	if(length(parems) = 0) then []
	else (buildArgMap(getP(tokens, "", [], 0), parems, [], funMap, paremMap))
	end
in 
if(length(tokens)) = 0 then nl
else if(isFunction(funMap, List.hd(tokens))) then removeFunctions(removeUntilEndOfFunction(tokens), nl @[
evaluateFunction(
mapGetValue(funMap, List.hd(tokens)), 
	getArguments(List.tl(List.tl(tokens)), getTokens(#" " , mapGetValue(paremMap, List.hd(tokens))), funMap, paremMap), 
funMap, paremMap)

], funMap, paremMap)
else removeFunctions(List.tl(tokens), nl @ [List.hd(tokens)], funMap, paremMap)
end

(*Evaluates a line and returns an integer value*)
fun evaluateIntLine(line : string, varMap : string list list, funMap, paremMap) =
let 
val y = (removeSpaces(line))
val x = (tokenize(y, []))
val z = fillInVariables(x, [], varMap)
val c = removeFunctions(z, [], funMap, paremMap)
val a = removeNegatives(c, [])
val i = generateStatement(a)
val postFix = toPostFix(i, [], [])
in
(print("\nAssining Value: " ^ evaluatePostFix(postFix, []) ^ "\n"); evaluatePostFix(postFix, []))
end

(*Breaks up a line into elements based on spaces*)
fun tokenizeLine(line : string) = getTokens(#" ", line)

(*Gets the right hand side of a assignment*)
fun getRHS(s) =
	let 
	fun go(str) = 
		let val l = explode(str)
		in 
		if(List.hd(l) = #"=") then implode(List.tl(l))
		else(go(implode(List.tl(l))))
		end
	in
	go(s)
end

fun getLHS(line : string) = List.nth(getTokens(#"=", line), 0)

(*Gets the variable name in a line*)
fun getName(line : string) = 
let
val tokens = getTokens(#" ", line)
in 
List.hd(List.tl(tokens))
end

fun removeUntilParen(line) = 
let 
	fun build(line, nl) = 
	let 
		val l = explode(line) 
		in
		if(length(l) = 0) then implode(nl)
		else if(List.hd(l) = #"(") then implode(nl)
		else if(List.hd(l) = #" ") then build(implode(List.tl(l)), nl)
		else build(implode(List.tl(l)), nl @[List.hd(l)]) 
	end
in
	build(line, [])
end

fun getFunctionName(line : string) = 
let
val tokens = getTokens(#" ", line)
val candidate = List.hd(List.tl(tokens))
in 
if(contains(candidate, ord(#"("))) then removeUntilParen(candidate)
else candidate
end

(*Gets type of line Example:  Assignent of Function*)
fun getLineFunction(line : string) = 
let val l = tokenizeLine(line)
in
if(List.hd(l) = "val") then ASSIGN
else if(List.hd(l) = "fun") then FUNCTION
else ERROR
end

(*Gets the type of a line.  Example is of type int or string*)	
fun getLineType(line : string) = INT

(*Handles an assignment statment*)
fun handleAssignment(line : string, varName : string, varMap : string list list, funMap, paremMap) =
if(getLineType(line) = INT) then (mapAdd(varMap, varName, evaluateIntLine(line, varMap, funMap, paremMap)))
else mapAdd(varMap, varName, "Error")

(*Evalutes a line and adds the value to the variable*)
fun computeAssignment(line : string, varMap : string list list, funMap, paremMap) = handleAssignment(getRHS(line), getName(line), varMap, funMap, paremMap)

(*Returns a string removing everything before the arguments*)
fun removeUntilArguments(s : string) = 
	let 
		val l = explode(s)
	in 
	if(length(l) = 0) then implode(l)
	else if(List.hd(l) = #"(") then implode(List.tl(l)) 
	else removeUntilArguments(implode(List.tl(l))) 
end

(*Takes in a line, and returns paremeters map with fun name as key and value of parameters seperated by a space*)
fun getParamterString(s : string, paremMap : string list list) = 
let
	fun parameterString(l : string list, ps : string) = 
		if(List.hd(l) = ")") then ps  
		else if(List.hd(l) = ",") then parameterString(List.tl(l), ps)
		else parameterString(List.tl(l), ps ^ " " ^ List.hd(l))
	
	val y = (removeSpaces(removeUntilArguments(s)))
	val x = (tokenize(y, []))
		in 
		if(contains(getLHS(s), ord(#"("))) then mapAdd(paremMap, getFunctionName(s), implode(List.tl(explode(parameterString(x, "")))))  else mapAdd(paremMap, getName(s), "")

end

fun getPString(s : string, paremMap : string list list) = 
let
	fun parameterString(l : string list, ps : string) = 
		if(List.hd(l) = ")") then ps  
		else if(List.hd(l) = ",") then parameterString(List.tl(l), ps)
		else parameterString(List.tl(l), ps ^ " " ^ List.hd(l))
	
	val y = (removeSpaces(removeUntilArguments(s)))
	val x = (tokenize(y, []))
		in 
implode(List.tl(explode(parameterString(x, ""))))
end

fun handleFunction(line : string, funList : string list list) =  (print("Fun: " ^ getFunctionName(line) ^"\n"); mapAdd(funList, getFunctionName(line), getRHS(line)))

(*Main function of the program*)
fun interpret(inFile : string, outFile : string) =
	let
		val _ = print("SML INTERPRETER\n\n")
		val inStream = TextIO.openIn inFile
		val readLine = TextIO.inputLine inStream
		val outStream = TextIO.openOut outFile
		val blank = []
			fun helper(readLine : string option, varMap : string list list, funMap :string list list, paremMap : string list list) =
				case readLine of
					NONE => (TextIO.closeIn inStream; TextIO.closeOut outStream; print("\n\n"))
					| SOME(c) => (
					let 
					val line = removeEnd(explode(c))
					in
					if(getLineFunction(line) = ASSIGN) then (print("Val: " ^ getName(line)); helper(TextIO.inputLine inStream, computeAssignment(line, varMap, funMap, paremMap), funMap, paremMap))
					else (helper(TextIO.inputLine inStream, varMap, handleFunction(line, funMap), getParamterString(line, paremMap)))
					end)
	in 
		helper(readLine, blank, blank, blank)
	end
val _ = interpret("input.txt", "output.txt")